package me.fponzi.tlaplusformatter;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.fail;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

/**
 * Semantic preservation test against the tlaplus/Examples repository.
 * <p>
 * This test validates that the formatter preserves semantics when formatting
 * real-world TLA+ specs. It parses the original file, formats it, parses the
 * formatted output, and compares the ASTs.
 * <p>
 * Configuration:
 * - System property: -Dtlaplus.examples.path=/path/to/Examples
 * - Environment variable: TLAPLUS_EXAMPLES_PATH
 * git clone https://github.com/tlaplus/Examples.git /tmp/tlaplus-examples
 * git clone --depth 1 https://github.com/tlaplus/tlapm.git /tmp/tlapm
 * git clone --depth 1 https://github.com/apalache-mc/apalache.git /tmp/apalache
 * cd /tmp && curl -LO
 * https://github.com/tlaplus/CommunityModules/releases/latest/download/CommunityModules-deps.jar &&
 * unzip -o CommunityModules-deps.jar -d CommunityModules
 * Usage:
 * ./gradlew semanticPreservationTest -Dtlaplus.examples.path=/path/to/Examples
 * <p>
 * This test is excluded from regular test runs.
 */
public class TlaPlusExamplesSemanticPreservationTest {

    private static final AtomicInteger passedCount = new AtomicInteger(0);
    private static final AtomicInteger skippedCount = new AtomicInteger(0);
    private static final AtomicInteger failedCount = new AtomicInteger(0);
    private static final List<String> failedFiles = new ArrayList<>();

    private static String getExamplesPath() {
        String path = System.getProperty("tlaplus.examples.path");
        if (path == null || path.isEmpty()) {
            path = System.getenv("TLAPLUS_EXAMPLES_PATH");
        }
        return path;
    }

    private static String getFileFilter() {
        String filter = System.getProperty("tlaplus.examples.filter");
        if (filter == null || filter.isEmpty()) {
            filter = System.getenv("TLAPLUS_EXAMPLES_FILTER");
        }
        return filter;
    }

    @TestFactory
    Stream<DynamicTest> semanticPreservationTests() throws IOException {
        String examplesPath = getExamplesPath();

        if (examplesPath == null || examplesPath.isEmpty()) {
            return Stream.of(DynamicTest.dynamicTest(
                    "Semantic preservation test skipped - no path configured",
                    () -> assumeTrue(false,
                            "tlaplus/Examples path not configured. " +
                                    "Set -Dtlaplus.examples.path=/path/to/Examples or TLAPLUS_EXAMPLES_PATH environment variable.")
            ));
        }

        Path examplesDir = Path.of(examplesPath);
        if (!Files.exists(examplesDir) || !Files.isDirectory(examplesDir)) {
            return Stream.of(DynamicTest.dynamicTest(
                    "Semantic preservation test skipped - path does not exist",
                    () -> assumeTrue(false,
                            "tlaplus/Examples path does not exist or is not a directory: " + examplesPath)
            ));
        }

        String fileFilter = getFileFilter();

        List<Path> tlaFiles = Files.walk(examplesDir)
                .filter(Files::isRegularFile)
                .filter(p -> p.toString().endsWith(".tla"))
                .filter(p -> fileFilter == null || fileFilter.isEmpty() || p.toString().contains(fileFilter))
                .filter(TlaPlusExamplesSemanticPreservationTest::filenameMatchesModule)
                .sorted()
                .collect(Collectors.toList());

        if (tlaFiles.isEmpty()) {
            String msg = fileFilter != null && !fileFilter.isEmpty()
                    ? "No .tla files found matching filter '" + fileFilter + "' in: " + examplesPath
                    : "No .tla files found in: " + examplesPath;
            return Stream.of(DynamicTest.dynamicTest(
                    "Semantic preservation test skipped - no .tla files found",
                    () -> fail(msg)
            ));
        }

        System.out.println("Found " + tlaFiles.size() + " .tla files to test" +
                (fileFilter != null && !fileFilter.isEmpty() ? " (filter: " + fileFilter + ")" : ""));

        return tlaFiles.stream().map(tlaFile ->
                DynamicTest.dynamicTest(
                        examplesDir.relativize(tlaFile).toString(),
                        () -> testSemanticPreservation(tlaFile)
                )
        );
    }

    /**
     * Check that the filename matches the MODULE name declared inside the file.
     * SANY requires these to match; files with mismatches are inherently untestable.
     */
    private static boolean filenameMatchesModule(Path p) {
        String basename = p.getFileName().toString().replaceFirst("\\.tla$", "");
        try {
            for (String line : Files.readAllLines(p)) {
                var m = java.util.regex.Pattern.compile("----\\s*MODULE\\s+(\\w+)").matcher(line);
                if (m.find()) {
                    return basename.equals(m.group(1));
                }
            }
        } catch (IOException ignored) {
        }
        return true; // if we can't determine, include it
    }

    private void testSemanticPreservation(Path tlaFilePath) {
        File tlaFile = tlaFilePath.toFile();

        // Step 1: Parse original file
        TLAPlusFormatter originalFormatter;
        try {
            originalFormatter = new TLAPlusFormatter(tlaFile);
        } catch (Exception e) {
            // Files that SANY cannot parse should fail — all external modules
            // (TLAPS, Apalache, Community Modules) must be available.
            skippedCount.incrementAndGet();
            failedFiles.add(tlaFilePath.toString() + " (original unparseable: " + getShortError(e) + ")");
            fail("Original file cannot be parsed (missing module?): " + tlaFilePath.getFileName() + " - " + e.getMessage());
            return;
        }

        // Step 2: Format the file
        String formattedOutput;
        try {
            formattedOutput = originalFormatter.getOutput();
        } catch (Exception e) {
            // Formatter crashes are actual failures
            failedCount.incrementAndGet();
            failedFiles.add(tlaFilePath.toString() + " (format error: " + e.getMessage() + ")");
            fail("Formatter crashed on file " + tlaFilePath + ": " + e.getMessage());
            return;
        }

        // Step 3: Parse formatted output
        // Write formatted output in place (backup original, restore after test)
        // This ensures sibling files (for INSTANCE) are available
        Path backupPath = Path.of(tlaFilePath + ".old");
        TLAPlusFormatter formattedFormatter;
        try {
            // Backup original file
            Files.move(tlaFilePath, backupPath);

            // Write formatted output to original location
            Files.writeString(tlaFilePath, formattedOutput);

            // Parse formatted output (sibling .tla files are now available)
            formattedFormatter = new TLAPlusFormatter(tlaFile);
        } catch (Exception e) {
            String errorMsg = e.getMessage();
            // Missing imports in formatted output should fail — all external modules must be available
            if (errorMsg != null && errorMsg.contains("Cannot find source file for module")) {
                skippedCount.incrementAndGet();
                failedFiles.add(tlaFilePath.toString() + " (formatted output missing module: " + errorMsg + ")");
                fail("Formatted output has unresolvable imports: " + tlaFilePath.getFileName() + " - " + errorMsg);
                return;
            }
            // Other parse errors are actual failures
            failedCount.incrementAndGet();
            failedFiles.add(tlaFilePath.toString() + " (formatted output parse error: " + errorMsg + ")");
            fail("Formatted output cannot be parsed for file " + tlaFilePath + ": " + errorMsg +
                    "\n\nFormatted output:\n" + formattedOutput);
            return;
        } finally {
            // Always restore original file
            try {
                Files.deleteIfExists(tlaFilePath);
                Files.move(backupPath, tlaFilePath);
            } catch (IOException e) {
                System.err.println("WARNING: Failed to restore " + tlaFilePath + " from backup: " + e.getMessage());
            }
        }

        // Step 4: Compare ASTs
        boolean astsEqual;
        try {
            astsEqual = Utils.assertAstEquals(originalFormatter.root, formattedFormatter.root);
        } catch (AssertionError e) {
            failedCount.incrementAndGet();
            failedFiles.add(tlaFilePath.toString() + " (AST mismatch: " + e.getMessage() + ")");
            fail("AST comparison failed for file " + tlaFilePath + ": " + e.getMessage());
            return;
        }

        if (!astsEqual) {
            failedCount.incrementAndGet();
            failedFiles.add(tlaFilePath.toString() + " (ASTs differ)");
            fail("Semantic preservation violated: ASTs differ for file " + tlaFilePath);
            return;
        }

        passedCount.incrementAndGet();
    }

    private static String getShortError(Exception e) {
        String msg = e.getMessage();
        if (msg == null) return e.getClass().getSimpleName();
        // Extract just the key part of the error
        if (msg.contains("Cannot find source file for module")) {
            int idx = msg.indexOf("Cannot find source file for module");
            int end = msg.indexOf("\n", idx);
            return end > 0 ? msg.substring(idx, end) : msg.substring(idx, Math.min(idx + 60, msg.length()));
        }
        return msg.length() > 80 ? msg.substring(0, 80) + "..." : msg;
    }

    @AfterAll
    static void printSummary() {
        System.out.println("\n========================================");
        System.out.println("Semantic Preservation Test Summary");
        System.out.println("========================================");
        System.out.println("Passed:  " + passedCount.get());
        System.out.println("Skipped: " + skippedCount.get());
        System.out.println("Failed:  " + failedCount.get());

        if (!failedFiles.isEmpty()) {
            System.out.println("\nFailed files:");
            for (String file : failedFiles) {
                System.out.println("  - " + file);
            }
        }
        System.out.println("========================================\n");

        // Assert no files were skipped - all external modules should be available
        assertEquals(0, skippedCount.get(),
                "No files should be skipped. Ensure TLAPS, Apalache, and Community Modules are available.");
    }
}
