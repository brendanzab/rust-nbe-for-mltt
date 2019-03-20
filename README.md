# rust-nbe-for-mltt

Danny Gratzer's implementation of [Normalization by Evaluation for Martin-Löf
Type Theory][nbe-for-mltt], ported to Rust. This will probably become the basis
for a new front-end for [Pikelet](https://github.com/pikelet-lang/pikelet).

In traditional type checking and normalization that uses [DeBruijn indices][de-bruijn-indices],
you are required to shift variable indices whenever you open up binders. This
is extremely expensive, and rules out future optimizations, like [using
visitors][visitors] to reduce the number of intermediate allocations as the AST
is traversed. This implementation avoids these problems by using a "semantic
type checking"  algorithm that uses DeBruijn indices for the core syntax, and
DeBruijn levels in the syntax of the semantic domain.

| Syntax        | Binding method              | Example                         |
|---------------|-----------------------------|---------------------------------|
| Concrete      | Nominal                     | `λz. (λy. y (λx. x)) (λx. z x)` |
| Core          | Nameless (DeBruijn Indices) | `λ . (λ . 0 (λ . 0)) (λ . 1 0)` |
| Domain        | Nameless (DeBruijn Levels)  | `λ . (λ . 1 (λ . 2)) (λ . 0 1)` |

[nbe-for-mltt]: https://github.com/jozefg/nbe-for-mltt
[de-bruijn-indices]: https://en.wikipedia.org/wiki/De_Bruijn_index
[visitors]: https://github.com/pikelet-lang/pikelet/issues/75

## TODO

- [x] Convert data types to Rust
- [x] Port NbE and bidirectional type checking
- [x] Add a parser for the concrete syntax
- [x] Desugaring of concrete syntax to core syntax
- [x] Resugaring of core syntax to concrete syntax
- [x] Pretty printing
- [x] Add a REPL
- [x] Add span information to ASTs to improve diagnostics
- [ ] Pattern matching elaboration
- [x] Dependent record types
- [x] Primitive operations
- [ ] Add eta rules to normalizer
- [ ] Metavariable solving
- [ ] Integration tests
  - [ ] Parse (pass)
  - [ ] Parse (fail)
  - [x] Type checking (pass)
  - [ ] Type checking (fail)
  - [ ] Normalization tests
- [ ] Error recovery in:
  - [x] Lexer
  - [ ] Parser
  - [ ] Elaborator
  - [ ] Validator
- [ ] Experiment with using visitors
- [ ] Preserve pretty names through type checking and normalization
- [ ] Use arena allocation rather than reference counting
- [ ] Type preserving compilation
