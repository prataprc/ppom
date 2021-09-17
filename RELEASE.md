0.7.0
-----

* **Breaking change** to mdb::Mdb.
  Rename Mdb type to OMap, it is resolved under `mdb` module.
  Now is this more inline with other variants of OMap with just one
  feature, which is, it is partially persistent. That is all writes are
  serialized and all the threads tend to access the same root using
  a spin-lock and holds a read reference.
* omap: improve fuzzy testing.
  * generate op for random() method.
  * randomly skew the ops towards remove operation.
* omap: improve test cases using u16 keys and u32 keys
* perf: fix perf binary for test OMap, rc::OMap, arc::OMap.
* cargo: make arbitrary dependency optional. Required only for testing
   and for bin/perf.
* code refactor/re-organisation.
  * mdb file renames.

0.6.0
-----

* Mdb type: implement `delete_count()`, `commit()` API.
* perf: fine tune.
* rustdoc
* enable `debug` for `test` and `bench` profile.
* ci-scripts
* package maintanence

Refer to [release-checklist][release-checklist].

[release-checklist]: https://prataprc.github.io/rust-crates-release-checklist.html
