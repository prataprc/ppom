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

* [Wikipedia link][wiki-llrb] on LLRB algorithm.
* [Wikipedia link][wiki-pers] on persistent data structure.
* [Discussion][disc1] on the design choice over get() and range() API.

Contribution
------------

* Simple workflow. Fork - Modify - Pull request.
* Before creating a PR,
  * Run `make build` to confirm all versions of build is passing with
    0 warnings and 0 errors.
  * Run `check.sh` with 0 warnings, 0 errors and all testcases passing.
  * Run `perf.sh` with 0 warnings, 0 errors and all testcases passing.
  * [Install][spellcheck] and run `cargo spellcheck` to remove common spelling mistakes.
* [Developer certificate of origin][dco] is preferred.

[wiki-llrb]: https://en.wikipedia.org/wiki/Left-leaning_red%E2%80%93black_tree
[wiki-pers]: https://en.wikipedia.org/wiki/Persistent_data_structure
[disc1]: https://users.rust-lang.org/t/what-would-be-proper-api-for-index-get/28730/5
[dco]: https://developercertificate.org/
