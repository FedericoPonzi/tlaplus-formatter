## TLA<sup>+</sup> formatter configuration

The TLA<sup>+</sup> formatter is very flexible: the default used is described in this reference style guide, but each part is very configurable.
It is possible to define a user level config, and a project level config. If there is no project-level config, the user-level one will be used instead.
The config is serialized as a [toml](https://toml.io/en/) file.

## Full example:
This is the complete config file that can be copy-pasted and personalized. It's configured with the default values already.
You can also use `tlaplusformatter --sample-config > ~/.tlaplus-formatter/config.toml` to kickstart your user level config.
```
[general]
indentSizeSpaces = 4
startDefinitionOnNewLine = true
alignDefinitionWithDeclaration = true
[keywords.module]
Dashes = Ignore
Equals = Ignore
[keyword.extends]
MultipleSeparateLines = true
```


```
Template:
## name / ``
### Configuration
This is the default setting:
```
```
```

## General settings / `general`
These settings define general and default behaviors. Some of them can be tuned per keyword.
```
[general]
indentSizeSpaces = 4
startDefinitionOnNewLine = true
alignDefinitionWithDeclaration = true
```
### `startDefinitionOnNewLine: boolean`
The general default to start all definitions on a new line.
* Possible value: `true` or `false`.
* Default value: `true`.
  Example with value `true`:
```
EXTENDS
        TLC
MyOperator == 
              TRUE
```
Example with value `false`:
```
EXTENDS TLC
MyOperator == TRUE
```



### `alignDefinitonWithDeclaration: boolean`
Align or not the definitions with the declaration. When false, the next line will be indented by `indentSizeSpaces`.
* Possible value: `true` or `false`.
* Default value: `true`.
  Example with value `true`:
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
Example with value `false`, assuming `indentSizeSpaces` of 2:
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

## Module / `keywords.module`
A module is defined as:
* five or more dashes,
* the keyword MODULE,
* the module's name
* Four or more dashes.
  Four or more equal (=) symbols are used to define the end of the module.

### Recommendation
Use only 4 dashes and 4 equals:
```
---- MODULE ----
====
```

### Configuration
This is the default setting:
```
[keywords.module]
Dashes = Ignore
Equals = Ignore
```
* `Dashes`: a number or `Ignore`. Modify the behavior for handling the dashes before and after the module keyword.
    * Number (e.g. `5`): It will rewrite the number of dashes to this number.
    * Ignore: It won't change them.
* `Equals`: a number or `Ignore`. Modify the behavior for handling the dashes before and after the module keyword.
    * Number (e.g. `5`): It will rewrite the number of dashes to this number.
    * Ignore: It won't change them.

## Extends / `keyword.extends`
`Extends` is defined by:
* The Extends keyword
* One or more comma-separated module names
```
EXTENDS TLC, Naturals
```
### Configuration
This is the default setting:
```
[keyword.extends]
MultipleSeparateLines = true
startDefinitionOnNewLine = true
```
* `MultipleSeparateLines`: `boolean`. When set to `true`, if there are multiple extended modules the list will start on a new line.

## Variable[S] / `keywords.variable`
Defined by `VARIABLE` or `VARIABLES` keywords, followed by one or more comma separated values.

### Configuration
This is the default setting:
```
[keyword.extends]
MultipleSeparateLines = true
startDefinitionOnNewLine = true
```