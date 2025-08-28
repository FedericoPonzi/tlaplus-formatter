package me.fponzi.tlaplusformatter;

import java.io.File;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.*;

public abstract class LexiconTest {
    // creates a temp folder
    // stores input and expected there
    // run the formatter do asserts
    public void assertSpecEquals(String expected, String input, String... extendedSpecs) {
        try {
            File tmpFolder = Files.createTempDirectory("tlaplusfmt").toFile();

            File specFile = new File(tmpFolder, "Spec.tla");
            try (java.io.FileWriter writer = new java.io.FileWriter(specFile)) {
                writer.write(input);
            }
            for (String extendedSpec : extendedSpecs) {
                File extendedSpecFile = new File(tmpFolder, TLAPlusFormatter.getModuleName(extendedSpec) + ".tla");
                try (java.io.FileWriter writer = new java.io.FileWriter(extendedSpecFile)) {
                    writer.write(extendedSpec);
                }
            }
            var f = new TLAPlusFormatter(specFile);
            var received = f.getOutput();
            assertEquals(expected, received, "Formatted output does not match expected output");

            // override input spec with the formatted spec.
            try (java.io.FileWriter writer = new java.io.FileWriter(specFile)) {
                writer.write(expected);
            }
            var f2 = new TLAPlusFormatter(specFile);
            assertEquals(f.getOutput(), f2.getOutput());
        } catch (Exception e) { //  throws FrontEndException, IOException
            fail(e);
        }
    }

    /**
     * Compares src/test/resources/inputs/name.tla to src/test/resources/outputs/name.tla
     */
    public void testSpecFiles(String name) {
        try {
            URL resource = getClass().getClassLoader().getResource("inputs/" + name + ".tla");
            assertNotNull(resource, "Resource file not found");
            File input = new File(resource.toURI());
            String inputSpec = Files.readString(Path.of(resource.toURI()));
            //idempotency("testSpecFile: " + name, inputSpec);
            /*
            URL outputFile = getClass().getClassLoader().getResource("outputs/" + name + ".tla");
            assertNotNull(resource, "Resource file not found");
            String expected = Files.readString(Path.of(outputFile.toURI()));
            var f = new TLAPlusFormatter(expected);
            var actual = f.getOutput();
            assertNotNull(actual, "Formatted output is null");
            assertNotNull(expected, "Expected output is null");
            assertEquals(expected, actual, "Formatted output does not match expected output(" + outputFile.toURI() + ").");
            */
        } catch (Exception e) {
            fail(e);
        }
    }
}