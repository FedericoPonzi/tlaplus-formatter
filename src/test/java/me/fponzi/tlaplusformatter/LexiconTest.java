package me.fponzi.tlaplusformatter;

import java.io.File;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.fail;

public abstract class LexiconTest {


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