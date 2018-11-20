# rust-nbe-for-mltt

Danny Gratzer's implementation of [Normalization by Evaluation for Martin-Löf
Type Theory](https://github.com/jozefg/nbe-for-mltt), ported to Rust.

The nice thing about this algorithm is that it does not require shifting of
debruijn indices during type checking and normalization, due to the way it uses
DeBruijn indices for the surface syntax, and DeBruijn levels in the value syntax.
