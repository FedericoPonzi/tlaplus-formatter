## TLA<sup>+</sup> formatter

[![CI](https://github.com/FedericoPonzi/tlaplus-formatter/actions/workflows/ci.yml/badge.svg)](https://github.com/FedericoPonzi/tlaplus-formatter/actions/workflows/ci.yml)

<p align="center"><img alt="temporary tla+ formatter logo" src="assets/tlaplus-formatter-temp-logo.jpg" width="250"></p>

This is a formatter for the TLA<sup>+</sup> language.

It uses tlaplus tools' SANY library to parse your specification, and it applies some (at the moment) predefined format
to it.

## Project Goals:

* A formatter for the TLA+ language. Pluscal is (currently) not a priority.
* Configurable: provide sane defaults.
* Minimal: never add useless chars (no extra spaces or extra newlines)
* Reliable: It should never break any spec nor change its meaning. No configuration permutation should ever lead to a broken specs.
* Stable: Applying the formatter to the output of a previous formatter run should not change it.
* Fast.

## Configurations:

If you have specific requests for configuration options you would like to have, please consider opening an issue.

Currently, the idea is to follow the same ideas behind rustfmt. A user level formatter config and a project level
formatter config.

## Example

To see some examples of current reformatting, compare:

* HourClock.tla:
    * [before](https://github.com/FedericoPonzi/tlaplus-formatter/blob/main/src/test/resources/inputs/HourClock.tla)
      and [after](https://github.com/FedericoPonzi/tlaplus-formatter/blob/main/src/test/resources/outputs/HourClock.tla)
* TowerOfHanoi.tla:
    * [before](https://github.com/FedericoPonzi/tlaplus-formatter/blob/main/src/test/resources/inputs/TowerOfHanoi.tla)
      and [after](https://github.com/FedericoPonzi/tlaplus-formatter/blob/main/src/test/resources/outputs/TowerOfHanoi.tla)
* Stones.tla:
    * [before](https://github.com/FedericoPonzi/tlaplus-formatter/blob/main/src/test/resources/inputs/Stones.tla)
      and [after](https://github.com/FedericoPonzi/tlaplus-formatter/blob/main/src/test/resources/outputs/Stones.tla)

More examples are in the test/java/resources/{inputs|outputs} folders. These sources are taken from the TLA+ Examples
repo.

## How to run

Download the latest JAR from the [Releases](https://github.com/FedericoPonzi/tlaplus-formatter/releases) page, or from the artifacts section of the latest [CI build](https://github.com/FedericoPonzi/tlaplus-formatter/actions/workflows/ci.yml).

You will need at least Java 11 (the same requirement as tlatools).

Unzip the file, and you can invoke the formatter like this:

```
java -jar tlaplus-formatter.jar <INFILE> [OUTFILE]
```

It will print your reformatted spec in output. If the optional "OUTFILE" parameter is specified, it will write the
output to that file.
You can use the input file as the output file as well. Run with `-help` parameter for the help text.

## VSCode integration

It's a work in progress, see [PR-327](https://github.com/tlaplus/vscode-tlaplus/pull/327/files) on vscode-tlaplus repo.

## Limitations

Because it uses SANY underneath (TLC's parser), your spec needs to first succeed SANY's
parsing process; otherwise the formatter won't be able to reformat your file.

## Acknowledgments

This project uses [prettier4j](https://github.com/opencastsoftware/prettier4j) by Opencast Software, which does the heavy lifting of implementing the Wadler-Lindig pretty-printing algorithm in Java.

