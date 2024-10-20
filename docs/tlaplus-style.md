# Formatter settings and TLA<sup>+</sup> style guide 
This document describes the formatter settings and provides an opinionated reference style guide for writing TLA<sup>+</sup> specifications. 

```
Template:
## name
### Definition
### Recommendation
### Configuration
This is the default setting:
```
```
```

## General
These settings define general and default behaviors. Some of them can be tuned per keyword.
```
[general]
indentSizeSpaces = 4
startDefinitonOnNewLine = true
alignDefinitionWithDeclaration = true
```
`startDefinitonOnNewLine`: boolean. When true, by default all definitions will start on a new line. For example:
```
EXTENDS
        TLC
MyOperator == 
              TRUE
```
`alignDefinitonWithDeclaration`: boolean. When true, by default all definition will be aligned with the declaration. For example:
```
MyOperator ==
              TRUE
HCnxt ==
         hr' = IF
                    hr # 12
               THEN
                    hr + 1
               ELSE
                    1
```
When false, the next line will use `indentSizeSpaces`. For example, assuming `indentSizeSpaces` of 4:
```
MyOperator ==
    TRUE
HCnxt ==
    hr' = IF
              hr # 12
          THEN
              hr + 1
          ELSE
              1
```


```
## Module
### Definition
A module is defined as:
* five or more dashes, 
* the keyword MODULE, 
* the module's name 
* five or more dashes.
Five or more equal symbols are used to define the end of the module.

### Recommendation
Use only 5 dashes and 5 equals:
```
---- MODULE ----
=====
```

### Configuration
This is the default setting:
```
[keywords.module]
Dashes = Ignore
Equals = Ignore
```
* Dashes: Number or `Ignore`. Modify the behavior for handling the dashes before and after the module keyword.
  * Number (e.g. `5`): It will rewrite the number of dashes to this number. 
  * Ignore: It won't change them.
* Equals: Number or `Ignore`. Modify the behavior for handling the dashes before and after the module keyword.
  * Number (e.g. `5`): It will rewrite the number of dashes to this number.
  * Ignore: It won't change them.

## Extends
`Extends` is defined by:
* The Extends keyword
* One or more comma-separated module names

### Recommendation
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

### Configuration
This is the default setting:
```
[keyword.extends]
MultipleStartNewLine = true
```
* `MultipleStartNewLine`: boolean or default. When set to True, if there are multiple extended modules the list will start on a new line.


