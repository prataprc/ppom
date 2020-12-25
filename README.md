Left Leaning Red Black Tree
===========================

[![Rustdoc](https://img.shields.io/badge/rustdoc-hosted-blue.svg)](https://docs.rs/llrb-index)

This package implements LLRB, Left Leaning Red Black, tree a popular
data structured, with following features:

* [x] Self-balancing data structure.
* [x] Optimized for in-memory index.
* [x] Each entry in LLRB instance correspond to a {Key, Value} pair.
* [x] Parametrised over Key type and Value type.
* [x] CRUD operations, via create(), set(), get(), delete() API.
* [x] Read optimized.
* [x] Full table scan, to iterate over all entries.
* [x] Range scan, to iterate between a ``low`` and ``high``.
* [x] Reverse iteration.

Note that this implementation of LLRB do not provide
``durability gaurantee`` and ``not thread safe``.

**Useful links**

* Refer to this [Wikipedia link][wikilink] for more information on LLRB algorithm.
* [Discussion][disc1] on the design choice over get() and range() API.

[wikilink]: https://en.wikipedia.org/wiki/Left-leaning_red%E2%80%93black_tree
[agpl]: https://github.com/bnclabs/llrb-index/blob/master/LICENSE
[#1]: https://github.com/bnclabs/llrb-index/issues/1
[disc1]: https://users.rust-lang.org/t/what-would-be-proper-api-for-index-get/28730/5
