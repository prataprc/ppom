0.5.0 (PENDING)
=====

0.4.0
=====

- Change the Range() API, make this similar to std-lib.
- Rewrite iter(), range() API. performance improvement by ~2x.
- Replace " as " type-casting with try\_into().unwrap().
- Implement Default trait for Depth type.
- Fix reverse API signature.
- Replace load\_from() with Extend trait.
- Improve unit-testing.

0.3.0
=====

- Implement Empty type that can be used as values.
- Breaking changes.
  * Rename LlrbError to Error.
  * Replace Clone implementation for Llrb with #[drive(Clone)]
  * Change return type for create() API.
- rustdoc.


0.2.0
=====

* Implement create() method on Llrb.
* Implement random() method on Llrb.
* Rename count() API to len() method on Llrb.
* Stats type and new stats() method on Llrb.
* validate() method should return Stats type.
* Tree depth statistics, in min, mean, max, percentiles.

0.1.0
=====

* Self-balancing data structure.
* Optimized for in-memory index.
* Each entry in LLRB instance correspond to a {Key, Value} pair.
* Parametrised over Key type and Value type.
* CRUD operations, via set(), get(), delete() API.
* Read optimized.
* Full table scan, to iterate over all entries.
* Range scan, to iterate between a ``low`` and ``high``.
* Reverse iteration.

Code Review checklist
=====================

* [ ] Review and check for un-necessary copy, and allocations.
* [ ] Review resize calls on `Vec`.
* [ ] Review (as ...) type casting, to panic on data loss.
* [ ] Reduce trait constraints for Type parameters on public APIs.
* [ ] Public APIs can be as generic as possible. Check whether there
      is a scope for `AsRef` or `Borrow` constraints.
* [ ] Document error variants.
* [ ] Check for dangling links in rustdoc.

Release Checklist
=================

* Bump up the version:
  * __major__: backward incompatible API changes.
  * __minor__: backward compatible API Changes.
  * __patch__: bug fixes.
* Cargo checklist
  * cargo +stable build; cargo +nightly build
  * cargo +stable doc; cargo +nightly doc
  * cargo +stable test; cargo +nightly test
  * cargo +nightly bench
  * cargo +nightly clippy --all-targets --all-features
  * cargo fix --edition --all-targets
* Travis-CI integration.
* Spell check.
* Create a git-tag for the new version.
* Cargo publish the new version.
* Badges
  * Build passing, Travis continuous integration.
  * Code coverage, codecov and coveralls.
  * Crates badge
  * Downloads badge
  * License badge
  * Rust version badge.
  * Maintenance-related badges based on isitmaintained.com
  * Documentation
  * Gitpitch
