* Implement `iter`, `range`, `reverse` as iterable over reference to
  value, instead of returning a clone of the value.
* Implement `iter_mut`, `range_mut`, `reverse_mut` for OMap.
* Implement iter(), range(), as double-ended iterator and remove
  reverse() method
* Mark Mdb and associted types/traits as deprecated, we are planning to
  use rdms::mdb
* Add perf numbers for OMap, rc::OMap, arc::OMap to README.md
* mdb::OMap is now partially persistent with all other things same as
  other variants. Add test case.

