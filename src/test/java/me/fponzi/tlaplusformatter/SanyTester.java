package me.fponzi.tlaplusformatter;

import me.fponzi.tlaplusformatter.format.TreeNode;

import java.io.File;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.*;

public abstract class SanyTester {
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

            assertTrue(compareAst(f.root, f2.root));

        } catch (Exception e) { //  throws FrontEndException, IOException
            fail(e);
        }
    }

    boolean compareAst(TreeNode root1, TreeNode root2) {
        if (root1.zero() != null) {
            for (int i = 0; i < root1.zero().length; i++) {
                if (!compareAst(root1.zero()[i], root2.zero()[i])) {
                    return false;
                }
            }
        }
        if (root1.one() != null) {
            for (int i = 0; i < root1.one().length; i++) {
                if (!compareAst(root1.one()[i], root2.one()[i])) {
                    return false;
                }
            }
        }
        return root1.getImage().equals(root2.getImage());
    }

    // TODO: compare AST of pre format and post format.

    /**
     * Compares src/test/resources/inputs/name.tla to src/test/resources/outputs/name.tla
     */
    public void testSpecFiles(String name) {
        try {
            URL resource = getClass().getClassLoader().getResource("inputs/" + name + ".tla");
            assertNotNull(resource, "Resource file not found");
            File input = new File(resource.toURI());

            URL outputFile = getClass().getClassLoader().getResource("outputs/" + name + ".tla");
            assertNotNull(resource, "Resource file not found");
            String expected = Files.readString(Path.of(outputFile.toURI()));
            var f = new TLAPlusFormatter(input);
            var actual = f.getOutput();
            assertNotNull(actual, "Formatted output is null");
            assertNotNull(expected, "Expected output is null");
            assertEquals(expected, actual, "Formatted output does not match expected output(" + outputFile.toURI() + ").");

            // here we use the downside of having SANY validating the spec
            // as an advantage to ensure the specs are valid.
            // also, the formatting should be stable.

            // initialize tlaplusfmt using output file path.
            // in this way, if the spec EXTENDS other specs, we can include them in the outputs resource folder.
            // For example see TowerOfHanoi.tla.
            // If output is an invalid spec, SANY will let us know.
            var f2 = new TLAPlusFormatter(new File(outputFile.toURI()));

            // the ast of the initial spec should match the ast of the output spec.
            assertTrue(compareAst(f.root, f2.root));

            try {
                // It should be a bit redundant with the compareAst above, but it's just an additional sanity check.
                // might remove later to keep tests fast
                actual = f2.getOutput();
                assertNotNull(actual, "Formatted output is null");
                assertEquals(expected, actual, "Second formatted output does not match expected output");
            } catch (Exception e) {
                fail(actual, e);
            }

        } catch (Exception e) {
            fail(e);
        }
    }
}
