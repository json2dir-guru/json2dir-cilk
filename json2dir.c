/* json2dir: create the directory tree a JSON document describes, in the current directory.
 * Implements RFC J2D-1 (https://github.com/kitsunoff/awesome-json2dir/blob/main/spec/rfc-json2dir.md).
 *
 * Cilk (OpenCilk) + POSIX libc, one file. Build:  clang -fopencilk -O2 -static -o json2dir json2dir.c
 *
 * Parallelism (fork-join):
 *   - validation: the members of every object are checked with cilk_for, combining the
 *     per-member results with an "and" reducer. Pure computation, no side effects.
 *   - writing: the members of one directory are created sequentially (so §5 replace/reuse
 *     decisions happen in a fixed order), then the object members (now real directories with
 *     distinct names) are filled in parallel with cilk_spawn. Distinct subdirectories never
 *     touch each other's entries, so the resulting tree does not depend on scheduling.
 */
#define _GNU_SOURCE
#include <cilk/cilk.h>
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

enum { T_OBJ, T_STR, T_ARR, T_OTHER };
#define MAX_DEPTH 1000

typedef struct Node Node;
typedef struct {
    char *name;
    size_t len;
    size_t idx; /* position in the document, to keep the last duplicate */
    Node *val;
} Member;
struct Node {
    int type;
    char *s; /* T_STR: decoded bytes */
    size_t len;
    Member *m; /* T_OBJ members (sorted, deduplicated) */
    Node **a;  /* T_ARR elements */
    size_t n;
};

static void die(const char *msg) {
    fprintf(stderr, "json2dir: %s\n", msg);
    exit(1);
}

static void *xalloc(size_t n) {
    void *p = calloc(1, n ? n : 1);
    if (!p) die("out of memory");
    return p;
}

/* ---------- §3: strict UTF-8 ---------- */
static int utf8_ok(const unsigned char *s, size_t n) {
    size_t i = 0;
    while (i < n) {
        unsigned c = s[i];
        size_t k;
        unsigned cp, min;
        if (c < 0x80) { i++; continue; }
        else if (c >= 0xC2 && c <= 0xDF) { k = 1; cp = c & 0x1F; min = 0x80; }
        else if (c >= 0xE0 && c <= 0xEF) { k = 2; cp = c & 0x0F; min = 0x800; }
        else if (c >= 0xF0 && c <= 0xF4) { k = 3; cp = c & 0x07; min = 0x10000; }
        else return 0;
        if (i + k >= n) return 0; /* truncated sequence */
        for (size_t j = 1; j <= k; j++) {
            if ((s[i + j] & 0xC0) != 0x80) return 0;
            cp = (cp << 6) | (s[i + j] & 0x3F);
        }
        if (cp < min || cp > 0x10FFFF || (cp >= 0xD800 && cp <= 0xDFFF)) return 0;
        i += k + 1;
    }
    return 1;
}

/* ---------- §3: strict JSON parser ---------- */
static const unsigned char *P, *E, *START;

static void ws(void) {
    while (P < E && (*P == ' ' || *P == '\t' || *P == '\n' || *P == '\r')) P++;
}

static void bad(const char *what) {
    fprintf(stderr, "json2dir: input is not valid JSON: %s at offset %ld\n", what, (long)(P - START));
    exit(1);
}

typedef struct { char *b; size_t n, cap; } Buf;
static void put(Buf *b, unsigned c) {
    if (b->n == b->cap) {
        b->cap = b->cap ? b->cap * 2 : 32;
        b->b = realloc(b->b, b->cap);
        if (!b->b) die("out of memory");
    }
    b->b[b->n++] = (char)c;
}
static void put_cp(Buf *b, unsigned cp) {
    if (cp < 0x80) put(b, cp);
    else if (cp < 0x800) { put(b, 0xC0 | (cp >> 6)); put(b, 0x80 | (cp & 0x3F)); }
    else if (cp < 0x10000) { put(b, 0xE0 | (cp >> 12)); put(b, 0x80 | ((cp >> 6) & 0x3F)); put(b, 0x80 | (cp & 0x3F)); }
    else { put(b, 0xF0 | (cp >> 18)); put(b, 0x80 | ((cp >> 12) & 0x3F)); put(b, 0x80 | ((cp >> 6) & 0x3F)); put(b, 0x80 | (cp & 0x3F)); }
}

static unsigned hex4(void) {
    unsigned v = 0;
    if (E - P < 4) bad("truncated \\u escape");
    for (int i = 0; i < 4; i++) {
        unsigned c = *P++, d = 0;
        if (c >= '0' && c <= '9') d = c - '0';
        else if (c >= 'a' && c <= 'f') d = c - 'a' + 10;
        else if (c >= 'A' && c <= 'F') d = c - 'A' + 10;
        else bad("bad \\u escape");
        v = v * 16 + d;
    }
    return v;
}

static char *parse_string(size_t *len) {
    Buf b = {0};
    P++; /* opening quote */
    for (;;) {
        if (P >= E) bad("unterminated string");
        unsigned c = *P++;
        if (c == '"') break;
        if (c < 0x20) bad("control character in string");
        if (c != '\\') { put(&b, c); continue; }
        if (P >= E) bad("unterminated string");
        c = *P++;
        switch (c) {
        case '"': put(&b, '"'); break;
        case '\\': put(&b, '\\'); break;
        case '/': put(&b, '/'); break;
        case 'b': put(&b, 8); break;
        case 'f': put(&b, 12); break;
        case 'n': put(&b, 10); break;
        case 'r': put(&b, 13); break;
        case 't': put(&b, 9); break;
        case 'u': {
            unsigned cp = hex4();
            if (cp >= 0xDC00 && cp <= 0xDFFF) bad("unpaired surrogate");
            if (cp >= 0xD800 && cp <= 0xDBFF) {
                if (E - P < 2 || P[0] != '\\' || P[1] != 'u') bad("unpaired surrogate");
                P += 2;
                unsigned lo = hex4();
                if (lo < 0xDC00 || lo > 0xDFFF) bad("unpaired surrogate");
                cp = 0x10000 + ((cp - 0xD800) << 10) + (lo - 0xDC00);
            }
            put_cp(&b, cp);
            break;
        }
        default: bad("bad escape");
        }
    }
    *len = b.n;
    put(&b, 0); /* terminator for convenience; len excludes it */
    return b.b;
}

static void parse_number(void) {
    if (P < E && *P == '-') P++;
    if (P >= E) bad("bad number");
    if (*P == '0') P++;
    else if (*P >= '1' && *P <= '9') while (P < E && *P >= '0' && *P <= '9') P++;
    else bad("bad number");
    if (P < E && *P == '.') {
        P++;
        if (P >= E || *P < '0' || *P > '9') bad("bad number");
        while (P < E && *P >= '0' && *P <= '9') P++;
    }
    if (P < E && (*P == 'e' || *P == 'E')) {
        P++;
        if (P < E && (*P == '+' || *P == '-')) P++;
        if (P >= E || *P < '0' || *P > '9') bad("bad number");
        while (P < E && *P >= '0' && *P <= '9') P++;
    }
}

static int member_cmp(const void *x, const void *y) {
    const Member *a = x, *b = y;
    size_t n = a->len < b->len ? a->len : b->len;
    int c = memcmp(a->name, b->name, n);
    if (c) return c;
    if (a->len != b->len) return a->len < b->len ? -1 : 1;
    return a->idx < b->idx ? -1 : a->idx > b->idx;
}

static Node *parse_value(int depth) {
    if (depth > MAX_DEPTH) bad("nesting too deep");
    ws();
    if (P >= E) bad("unexpected end of input");
    Node *v = xalloc(sizeof *v);
    if (*P == '{') {
        size_t cap = 0;
        v->type = T_OBJ;
        P++;
        ws();
        if (P < E && *P == '}') { P++; return v; }
        for (;;) {
            ws();
            if (P >= E || *P != '"') bad("expected member name");
            if (v->n == cap) {
                cap = cap ? cap * 2 : 8;
                v->m = realloc(v->m, cap * sizeof *v->m);
                if (!v->m) die("out of memory");
            }
            Member *m = &v->m[v->n];
            m->name = parse_string(&m->len);
            m->idx = v->n;
            ws();
            if (P >= E || *P != ':') bad("expected ':'");
            P++;
            m->val = parse_value(depth + 1);
            v->n++;
            ws();
            if (P < E && *P == ',') { P++; continue; }
            if (P < E && *P == '}') { P++; break; }
            bad("expected ',' or '}'");
        }
        /* §4.2: sort by UTF-8 bytes; for duplicate names keep the last occurrence */
        qsort(v->m, v->n, sizeof *v->m, member_cmp);
        size_t k = 0;
        for (size_t i = 0; i < v->n; i++) {
            if (i + 1 < v->n && v->m[i].len == v->m[i + 1].len &&
                memcmp(v->m[i].name, v->m[i + 1].name, v->m[i].len) == 0)
                continue;
            v->m[k++] = v->m[i];
        }
        v->n = k;
        return v;
    }
    if (*P == '[') {
        size_t cap = 0;
        v->type = T_ARR;
        P++;
        ws();
        if (P < E && *P == ']') { P++; return v; }
        for (;;) {
            if (v->n == cap) {
                cap = cap ? cap * 2 : 4;
                v->a = realloc(v->a, cap * sizeof *v->a);
                if (!v->a) die("out of memory");
            }
            v->a[v->n++] = parse_value(depth + 1);
            ws();
            if (P < E && *P == ',') { P++; continue; }
            if (P < E && *P == ']') { P++; break; }
            bad("expected ',' or ']'");
        }
        return v;
    }
    if (*P == '"') { v->type = T_STR; v->s = parse_string(&v->len); return v; }
    v->type = T_OTHER;
    if (E - P >= 4 && !memcmp(P, "true", 4)) { P += 4; return v; }
    if (E - P >= 5 && !memcmp(P, "false", 5)) { P += 5; return v; }
    if (E - P >= 4 && !memcmp(P, "null", 4)) { P += 4; return v; }
    if (*P == '-' || (*P >= '0' && *P <= '9')) { parse_number(); return v; }
    bad("unexpected character");
    return v;
}

/* ---------- §4: validation ---------- */
static int name_ok(const Member *m) {
    if (m->len == 0) return 0;
    if (m->len == 1 && m->name[0] == '.') return 0;
    if (m->len == 2 && m->name[0] == '.' && m->name[1] == '.') return 0;
    if (memchr(m->name, '/', m->len) || memchr(m->name, 0, m->len)) return 0;
    return 1;
}

/* Returns NULL if the value is valid, else a static description of the problem. */
static const char *value_problem(const Node *v) {
    if (v->type == T_STR || v->type == T_OBJ) return NULL;
    if (v->type == T_OTHER) return "numbers, true, false and null are not allowed";
    if (v->n != 2 || v->a[0]->type != T_STR || v->a[1]->type != T_STR)
        return "an array must be [\"link\", target] or [\"script\", content]";
    const Node *k = v->a[0];
    if (k->len == 4 && !memcmp(k->s, "link", 4)) {
        if (memchr(v->a[1]->s, 0, v->a[1]->len)) return "a link target cannot contain NUL";
        return NULL;
    }
    if (k->len == 6 && !memcmp(k->s, "script", 6)) return NULL;
    return "unknown array kind";
}

static void and_identity(void *v) { *(int *)v = 1; }
static void and_reduce(void *l, void *r) { *(int *)l = *(int *)l && *(int *)r; }

/* Parallel check: members of each object in parallel, combined with an "and" reducer. */
static int valid(const Node *obj) {
    int cilk_reducer(and_identity, and_reduce) ok = 1;
    cilk_for (size_t i = 0; i < obj->n; i++) {
        const Member *m = &obj->m[i];
        int good = name_ok(m) && value_problem(m->val) == NULL;
        if (good && m->val->type == T_OBJ) good = valid(m->val);
        if (!good) ok = 0;
    }
    return ok;
}

/* Sequential re-check, only run when the parallel pass failed, to report the first problem. */
static int report(const Node *obj, const char *where) {
    for (size_t i = 0; i < obj->n; i++) {
        const Member *m = &obj->m[i];
        size_t wl = strlen(where);
        char *path = xalloc(wl + m->len + 2);
        if (strcmp(where, ".") == 0) memcpy(path, m->name, m->len);
        else { memcpy(path, where, wl); path[wl] = '/'; memcpy(path + wl + 1, m->name, m->len); }
        const char *p = name_ok(m) ? value_problem(m->val) : "invalid name";
        if (p) { fprintf(stderr, "json2dir: %s: %s\n", path, p); return 1; }
        if (m->val->type == T_OBJ && report(m->val, path)) return 1;
        free(path);
    }
    return 0;
}

/* ---------- §5: writing ---------- */
static int failed; /* set atomically by any strand that hits an error */

static void fail_at(const char *path, const char *what, int err) {
    char msg[4096];
    int n = snprintf(msg, sizeof msg, "json2dir: %s: %s%s%s\n", path, what, err ? ": " : "", err ? strerror(err) : "");
    if (n > (int)sizeof msg - 1) n = sizeof msg - 1;
    if (write(2, msg, (size_t)n) < 0) { /* nothing more to do */ }
    __atomic_store_n(&failed, 1, __ATOMIC_SEQ_CST);
}

static int write_file(int dir, const char *name, const char *path, const Node *s, int exec) {
    /* O_EXCL|O_NOFOLLOW: never write through an entry that appeared after the unlink */
    int fd = openat(dir, name, O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_CLOEXEC, 0666);
    if (fd < 0) { fail_at(path, "cannot create file", errno); return -1; }
    size_t off = 0;
    while (off < s->len) {
        ssize_t w = write(fd, s->s + off, s->len - off);
        if (w < 0) {
            if (errno == EINTR) continue;
            fail_at(path, "write failed", errno);
            close(fd);
            return -1;
        }
        off += (size_t)w;
    }
    if (exec) {
        struct stat st;
        if (fstat(fd, &st) < 0 || fchmod(fd, (st.st_mode & 07777) | 0111) < 0) {
            fail_at(path, "cannot make executable", errno);
            close(fd);
            return -1;
        }
    }
    if (close(fd) < 0) { fail_at(path, "close failed", errno); return -1; }
    return 0;
}

static void apply(int dir, const Node *obj, const char *where);

/* Fill one (already existing) subdirectory; runs as a spawned strand. */
static void apply_sub(int parent, const char *name, const Node *obj, char *path) {
    int fd = openat(parent, name, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
    if (fd < 0) fail_at(path, "cannot open directory", errno);
    else {
        apply(fd, obj, path);
        close(fd);
    }
    free(path);
}

static void apply(int dir, const Node *obj, const char *where) {
    /* Phase 1 (sequential): create/replace every entry of this directory. */
    for (size_t i = 0; i < obj->n; i++) {
        const Member *m = &obj->m[i];
        const Node *v = m->val;
        size_t wl = strlen(where);
        char path[8192];
        if (strcmp(where, ".") == 0) snprintf(path, sizeof path, "%s", m->name);
        else snprintf(path, sizeof path, "%.*s/%s", (int)wl, where, m->name);

        struct stat st;
        int exists = fstatat(dir, m->name, &st, AT_SYMLINK_NOFOLLOW) == 0;
        if (!exists && errno != ENOENT) { fail_at(path, "cannot stat", errno); continue; }
        int isdir = exists && S_ISDIR(st.st_mode);

        if (v->type == T_OBJ) {
            if (isdir) continue; /* §5.1: reuse */
            if (exists && unlinkat(dir, m->name, 0) < 0) { fail_at(path, "cannot remove", errno); continue; }
            if (mkdirat(dir, m->name, 0777) < 0) fail_at(path, "cannot create directory", errno);
            continue;
        }
        if (isdir) { fail_at(path, "a directory is in the way", 0); continue; } /* §5.4 */
        if (exists && unlinkat(dir, m->name, 0) < 0) { fail_at(path, "cannot remove", errno); continue; }
        if (v->type == T_STR) write_file(dir, m->name, path, v, 0);
        else if (v->a[0]->len == 4) { /* link */
            if (symlinkat(v->a[1]->s, dir, m->name) < 0) fail_at(path, "cannot create symlink", errno);
        } else write_file(dir, m->name, path, v->a[1], 1);
    }
    if (__atomic_load_n(&failed, __ATOMIC_SEQ_CST)) return;

    /* Phase 2 (parallel): distinct subdirectories are independent, fill them concurrently. */
    for (size_t i = 0; i < obj->n; i++) {
        const Member *m = &obj->m[i];
        if (m->val->type != T_OBJ) continue;
        size_t wl = strlen(where);
        char *path = xalloc(wl + m->len + 2);
        if (strcmp(where, ".") == 0) memcpy(path, m->name, m->len);
        else { memcpy(path, where, wl); path[wl] = '/'; memcpy(path + wl + 1, m->name, m->len); }
        cilk_spawn apply_sub(dir, m->name, m->val, path);
    }
    cilk_sync;
}

int main(int argc, char **argv) {
    (void)argv;
    if (argc > 1) {
        fprintf(stderr, "usage: json2dir < document.json\n");
        return 2;
    }
    Buf in = {0};
    char chunk[65536];
    for (;;) {
        ssize_t r = read(0, chunk, sizeof chunk);
        if (r < 0) { if (errno == EINTR) continue; die("cannot read standard input"); }
        if (r == 0) break;
        for (ssize_t i = 0; i < r; i++) put(&in, (unsigned char)chunk[i]);
    }
    const unsigned char *s = (const unsigned char *)in.b;
    size_t n = in.n;
    if (!utf8_ok(s, n)) die("input is not valid UTF-8");
    if (n >= 3 && s[0] == 0xEF && s[1] == 0xBB && s[2] == 0xBF) { s += 3; n -= 3; } /* §3: BOM allowed */
    START = P = s;
    E = s + n;
    Node *root = parse_value(0);
    ws();
    if (P != E) bad("trailing data after the JSON value");
    if (root->type != T_OBJ) die("the root of the document must be an object");

    if (!valid(root)) {
        if (!report(root, ".")) die("invalid document");
        return 1;
    }
    /* files are created 0666 and directories 0777; the kernel applies the umask */
    apply(AT_FDCWD, root, ".");
    return failed ? 1 : 0;
}
