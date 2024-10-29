# Formatter settings and TLA<sup>+</sup> style guide 
This document provides an opinionated reference style guide for writing TLA<sup>+</sup> specifications. 

This document is what drives the default formatting behavior for the TLA<sup>+</sup> formatter.

## Blank lines
Separate items and statements by either zero or one blank lines (i.e., one or two newlines). E.g,
```
---------------------- MODULE HourClock ----------------------
EXTENDS Naturals, TLC
VARIABLE
         hr

HCini ==
         hr \in (1 .. 12)
HC ==
      HCini /\ [][HCnxt]_hr

==============================================================

```

## Alignments
If there is one module, it should be included in the same line
```
EXTENDS TLC
```
If there is more than one module, they should be on separated lines.
```
EXTENDS
        TLC, 
        ModuleA, 
        ModuleB
```



----

References: https://github.com/rust-lang/rust/tree/HEAD/src/doc/style-guide/src

