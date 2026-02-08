# Development

## Building

```bash
./gradlew build        # Build and run all tests + static analysis
./gradlew buildFatJar  # Build distributable fat JAR
./gradlew run --args="<INPUT_FILE> [OUTPUT_FILE]"  # Run the formatter
```

## CI:

The SemanticPreservationTest pulls, formats and validates all the specs from the Examples repo.

