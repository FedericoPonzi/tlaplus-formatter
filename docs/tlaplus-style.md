# Formatter settings and TLA<sup>+</sup> style guide 
This document provides an opinionated reference style guide for writing TLA<sup>+</sup> specifications. 

This document is what drives the default formatting behavior for the TLA<sup>+</sup> formatter.

> [!NOTE] 
> TLA<sup>+</sup> should be written like a poem. Short sentences and new lines with vertical alignment help bring 
> clarity when reading specs.

# Formatting conventions

### Indentation and line width

- Use spaces, not tabs.
- Each level of indentation must be 2 spaces (that is, all indentation
  outside of string literals and comments must be a multiple of 2).
- The maximum width for a line is 100 characters.

#### Block indent

Prefer block indent over visual indent:

```latex
\* Block indent
MySet == {
   1,
   2,
   3 }

\* Visual indent
MySet2 == { 1,
            2,
            3 }
```

This makes for smaller diffs (e.g., if `MySet2` is renamed in the above
example) and less rightward drift.

## Blank lines
Separate items and statements by either zero or one blank lines (i.e., one or two newlines). E.g,
```latex
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

### Comments

Prefer block comments (`(* ... *)`) to line comments (`\*`).

When using line comments, put a single space after the opening sigil.

Comments should be vertically aligned to the formula they refer to.

## Small items

### *small* items

In many places in this guide we specify formatting that depends on a code
construct being *small*. For example:

```latex
// Normal formatting
MyRecord == [
  beginLine |-> 46,
  beginColumn |-> 1,
  endLine |-> 46,
  endColumn |-> 18,
  module |-> "MCCRDT"
]

// "small" formatting
MySet == { 1, 2, 3 }
```

We leave it to individual tools to decide on exactly what *small* means. In
particular, tools are free to use different definitions in different
circumstances.

Some suitable heuristics are the size of the item (in characters) or the
complexity of an item (for example, that all components must be simple names,
not more complex sub-expressions). For more discussion on suitable heuristics,
see [this issue](https://github.com/rust-lang-nursery/fmt-rfcs/issues/47).


## Alignments
If there is one module, it should be included in the same line
```
EXTENDS TLC
```
If there is more than one module, they should be on separated lines.
```
EXTENDS TLC, 
        ModuleA, 
        ModuleB
```
Similarly, definitions should start on the same line.
```
Hours == 12

HCini == hr \in (1 .. 12)
```

### Data structures
Data structure with short content should be defined on the same line.
```
MySet = { 123 }
MySet == { 1, 2, 3 }
```
With multiple elements, the opening symbol should be on the same line while the definition should start onto the next line aligned by the == symbol.
```
MySet == [
  beginLine |-> 46,
  beginColumn |-> 1,
  endLine |-> 46,
  endColumn |-> 18,
  module |-> "MCCRDT" ]
```

----

References: https://github.com/rust-lang/rust/tree/HEAD/src/doc/style-guide/src

