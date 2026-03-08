## Upcoming: 0.3.0
* Operator definitions with conjunction/disjunction list bodies now break after `==`, improving VS Code code folding.

## 0.2.1
* Fix: no longer inserts spurious whitespace after symbolic prefix operators (`[]`, `<>`, `~`, `-`).
  For example, `[][Next]_vars` was incorrectly formatted as `[] [Next]_vars`.

## 0.2.0
* The tlaplus/Examples repo is pulled in for testing.
* Many fixes that came up after trying to reformat all the tla specs in the Example repo.
* TLA-Library option to add search path for tla modules like TLAPS and community modules.
* Libraries update
* Web integration

## 0.1.0

* Initial release of tlaplus-formatter
