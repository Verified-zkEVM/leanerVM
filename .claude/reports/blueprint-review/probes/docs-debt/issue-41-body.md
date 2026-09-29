Add native evaluations for the public index and bytecode columns, proved equal to their column-oracle answers. The bytecode column takes the public program explicitly and uses the existing sixteen-slot encoding, with instruction bits before slot bits.

Built on #18 for #32, following leanVM §§6.5 and 8.1 as part of the [leanth reuse request](https://github.com/Verified-zkEVM/leanerVM/issues/12). These are column-evaluation equalities; Rust execution correspondence remains separate.
