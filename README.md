[![Documentation](https://img.shields.io/badge/rustdoc-hosted-blue.svg)](https://docs.rs/ppom)

Persistent Ordered Map
======================


This package implements LLRB, Left Leaning Red Black, tree a popular
data structured, with following features:

* [x] Self-balancing data structure.
* [x] Each entry in OMap instance correspond to a {Key, Value} pair.
* [x] Parametrised over `key-type` and `value-type`.
* [x] CRUD operations, via set(), get(), remove() api.
* [x] Full table scan, to iterate over all entries.
* [x] Range scan, to iterate between a ``low`` and ``high``.
* [x] Reverse iteration.
* [x] Uses ownership model and borrow semantics to ensure safety.
* [x] Optimized for in-memory index.
* [x] Read optimized.

Refer to [rustdoc](https://docs.rs/ppom) for details.

**Useful links**

* Refer to this [Wikipedia link][wikilink] for more information on LLRB algorithm.
* [Discussion][disc1] on the design choice over get() and range() API.

Contribution
------------

* Simple workflow. Fork, modify and raise a pull request.
* Before making a PR,
  * Run `check.sh` with 0 warnings, 0 errors and all testcases passing.
  * Run `cargo +nightly clippy --all-targets --all-features` to fix clippy issues.
  * [Install][spellcheck] and run `cargo spellcheck` to remove common spelling mistakes.
* [Developer certificate of origin][dco] is preferred.

[wikilink]: https://en.wikipedia.org/wiki/Left-leaning_red%E2%80%93black_tree
[disc1]: https://users.rust-lang.org/t/what-would-be-proper-api-for-index-get/28730/5
