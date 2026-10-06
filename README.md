# json2dir-cilk

json2dir in Cilk (OpenCilk): create the directory tree a JSON document describes, validating and filling sibling subtrees in parallel.

    clang -fopencilk -O2 -static -o json2dir json2dir.c && ./json2dir < document.json
