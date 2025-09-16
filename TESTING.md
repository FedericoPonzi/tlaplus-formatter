# Testing Guide

This document describes the testing approach for the TLA+ formatter.

## Test Types

### Unit Tests
Individual component tests located in `src/test/java/me/fponzi/tlaplusformatter/` that test specific lexicon elements and formatting constructs.

### Integration Tests  
End-to-end tests that format complete TLA+ specifications and compare against expected outputs in `src/test/resources/`.

### Property-Based Tests
Automated tests using [jqwik](https://jqwik.net/) that generate hundreds of random TLA+ specifications to verify formatter correctness.

## Property-Based Testing

The `PropertyBasedFormatterTest` class uses property-based testing to automatically verify formatter behavior across a wide range of inputs. Property-based testing generates random test data and verifies that certain properties always hold, making it excellent for finding edge cases that manual testing might miss.

The implementation generates syntactically valid TLA+ specifications with:
- Random module names  
- 0-3 constant declarations
- Simple operator definitions using the declared constants

Two critical properties are tested:

**Semantic Preservation**: The formatter must preserve the meaning of the code. This is verified by parsing both the original and formatted specifications into Abstract Syntax Trees (ASTs) and ensuring they are structurally identical.

**Idempotence**: Running the formatter multiple times should produce the same result. This ensures the formatter reaches a stable state and doesn't continuously modify the code.

### Running Property-Based Tests

```bash
# Run all property-based tests (1000 examples each by default)
./gradlew test --tests PropertyBasedFormatterTest

# Run with specific seed for reproducible results
./gradlew test --tests PropertyBasedFormatterTest -Djqwik.seeds=123456789

# Run all tests
./gradlew test
```

The property-based tests automatically run 1000 random examples by default and include edge case testing, providing comprehensive coverage with minimal test code.

## Running Tests

```bash
# Run all tests
./gradlew test

# Run specific test class
./gradlew test --tests FormatterE2ETest

# Build and test
./gradlew build
```