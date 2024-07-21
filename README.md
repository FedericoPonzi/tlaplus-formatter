## TLA<sup>+</sup> formatter
This is a formatter for the TLA<sup>+</sup> language. 

It uses TLA's SANY library to parse your specification, and it applies some predefined format to it.

This is still ALPHA software, not everything is handled at the moment, so it might break your specs.

If you want to try it out, go to the build page of the latest commit, and download the "Package.zip" file from the artifact section at the bottom of the page ([Example](https://github.com/FedericoPonzi/tlaplus-formatter/actions/runs/10027954925)).

Unzip the file, and you can use the jar file in there like this:
```
java -jar tlaplus-formatter.jar <FILE>
```
It will print in output your reformatted spec.
