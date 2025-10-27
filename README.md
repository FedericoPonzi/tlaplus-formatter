## TLA<sup>+</sup> formatter

<p align="center"><img alt="temporary tla+ formatter logo" src="assets/tlaplus-formatter-temp-logo.jpg" width="250"></p>

This is a formatter for the TLA<sup>+</sup> language.

It uses tlaplus tools' SANY library to parse your specification, and it applies some (at the moment) predefined format
to it.

This is still _ALPHA_ software, feel free to try it out and leave feedback but be aware it might break your specs.

## Project Goals:

* A formatter for the TLA+ language. Pluscal is currently not a priority.
* It should be configurable but also provide sane defaults.
* It should never add useless chars (no extra spaces or extra newlines)
* It should never break any specs. No user configuration should ever lead to broken specs.
* The output should be stable. Applying the formatter to the output of a previous formatter run should not change it.
* It should be fast.

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

## Testing with TLA+-Smith

This project integrates [TLA+-Smith](https://github.com/fponzi/tlaplus-smith), a random TLA+ specification generator,
for comprehensive testing. TLA+-Smith helps ensure the formatter works correctly with a wide variety of TLA+ constructs
and edge cases.

## How to run

If you want to try it out, go to the build page of the latest commit and download the "tlaplus-formatter-jar.zip" file
from the
artifact section at the bottom of the
page ([Example](https://github.com/FedericoPonzi/tlaplus-formatter/actions/runs/10027954925)).

You will need at least java 11 (the same requirement as tlatools).

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

---

## Development

Some of the `constants` used in the code are coming from SANY's codebase, specifically from this file:
`src/tla2sany/st/SyntaxTreeConstants.java` (check [tlaplus repo](https://github.com/tlaplus/tlaplus/)).

