# Testing Guide

This document describes the testing approach for the TLA+ formatter.

## Test Types

### Unit Tests
Individual component tests located in `src/test/java/me/fponzi/tlaplusformatter/` that test specific lexicon elements and formatting constructs.

### Integration Tests  
End-to-end tests that format complete TLA+ specifications and compare against expected outputs in `src/test/resources/`.

## Running Tests

```bash
# Run all tests
./gradlew test

# Run specific test class
./gradlew test --tests FormatterE2ETest

# Build and test
./gradlew build
```