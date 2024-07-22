## TLA<sup>+</sup> formatter
This is a formatter for the TLA<sup>+</sup> language. 

It uses tlatools' SANY library to parse your specification, and it applies some (at the moment) predefined format to it.

This is still ALPHA software, not everything is handled at the moment, so it might break your specs.


## Example
To see an example, compare:
* HourClock.tla: [before](https://github.com/FedericoPonzi/tlaplus-formatter/blob/main/src/test/resources/inputs/HourClock.tla) and [after](https://github.com/FedericoPonzi/tlaplus-formatter/blob/main/src/test/resources/outputs/HourClock.tla).

## How to run
If you want to try it out, go to the build page of the latest commit, and download the "Package.zip" file from the artifact section at the bottom of the page ([Example](https://github.com/FedericoPonzi/tlaplus-formatter/actions/runs/10027954925)).

Unzip the file, and you can use the jar file in there like this:
```
java -jar tlaplus-formatter.jar <INFILE> [OUTFILE]
```

It will print in output your reformatted spec. If OUTFILE parameter is specified, it will write the output to that file.
You can use the input file as output file as well. Run with `-help` for the help text. 

## Run in vscode
It's work in progress, see [PR-327](https://github.com/tlaplus/vscode-tlaplus/pull/327/files) on vscode-tlaplus repo.


---

## Development
Some of the constant used in the code are coming from SANY's codebase, specifically from this file: `src/tla2sany/st/SyntaxTreeConstants.java` (check [tlaplus repo](https://github.com/tlaplus/tlaplus/)).
