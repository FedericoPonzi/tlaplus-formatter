package me.fponzi.tlaplusformatter;

import tla2sany.st.TreeNode;

import java.io.File;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.*;

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
            var f = new TLAPlusFormatter(input, new FormatConfig(80, 2));
            var actual = f.getOutput();
            //System.out.println(f.getOutput());
            // commented until issues are fixed:
            compareOutputSpec(name, actual, f.root);
        } catch (Exception e) {
            fail(e);
        }
    }

    void compareOutputSpec(String name, String actual, TreeNode root1) {
        try {
            URL outputFile = getClass().getClassLoader().getResource("outputs/" + name + ".tla");
            assertNotNull(outputFile, "Resource file not found");
            String expected = Files.readString(Path.of(outputFile.toURI()));
            assertNotNull(actual, "Formatted output is null");
            assertNotNull(expected, "Expected output is null");
            assertEquals(expected, actual, "Formatted output does not match expected output(" + outputFile.toURI() + ").");


            // initialize tlaplusfmt using output file path.
            // in this way, if the spec EXTENDS other specs, we can include them in the outputs resource folder.
            // For example see TowerOfHanoi.tla.
            // If output is an invalid spec, SANY will let us know.
            var f2 = new TLAPlusFormatter(new File(outputFile.toURI()));

            // the ast of the initial spec should match the ast of the output spec.
            // initial spec is the non-reformatted input. f2 is the parsed ast of the reformat output.
            assertTrue(compareAst(root1, f2.root));

            // It should be a bit redundant with the compareAst above, but it's just an additional sanity check.
            // might remove later to keep tests fast
            actual = f2.getOutput();
            assertNotNull(actual, "Formatted output is null");
            assertEquals(expected, actual, "Second formatted output does not match expected output");
        } catch (Exception e) {
            fail(actual, e);
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
        compareComments(root1, root2);
        // cannot use image, because for example `VARIABLE` get replaced with `VARIABLES`.
        if (root1.getKind() != root2.getKind()) {
            System.out.println("Node kinds do not match: " + root1.getKind() + " vs " + root2.getKind());
            System.out.println("Node image: " + root1.getImage() + " vs " + root2.getImage());
            System.out.println("Node Location" + root1.getLocation() + " vs " + root2.getLocation());
        }
        assertEquals(root1.getKind(), root2.getKind(), "Node kinds do not match");
        //assertEquals(root1.getImage(), root2.getImage());
        return root1.getKind() == root2.getKind();
    }

    void compareComments(TreeNode root1, TreeNode root2) {
        boolean hasComments1 = root1.getPreComments() != null && root1.getPreComments().length > 0;
        boolean hasComments2 = root2.getPreComments() != null && root2.getPreComments().length > 0;
        if (hasComments1 != hasComments2) {
            System.out.println("Node kind: " + root1.getKind());
        }
        assertEquals(hasComments1, hasComments2);
        if (hasComments1) {
            assertEquals(root1.getPreComments().length, root2.getPreComments().length);
            for (int i = 0; i < root1.getPreComments().length; i++) {
                assertEquals(root1.getPreComments()[i], root2.getPreComments()[i]);
            }
        }
    }
    // TODO: compare AST of pre format and post format.
}