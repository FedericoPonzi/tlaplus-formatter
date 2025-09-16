package me.fponzi.tlaplusformatter;

import me.fponzi.tlaplusformatter.exceptions.SanyFrontendException;
import tla2sany.st.TreeNode;

import java.io.IOException;

import static org.junit.jupiter.api.Assertions.*;

public class Utils {

    public static void assertUnchanged(String spec) {
        try {
            var f = (new TLAPlusFormatter(spec)).getOutput();
            assertEquals(spec, f);
            idempotency(spec);
        } catch (Exception e) {
            fail(e);
        }
    }

    static boolean assertAstEquals(TreeNode root1, TreeNode root2) {
        if (root1.zero() != null) {
            for (int i = 0; i < root1.zero().length; i++) {
                if (!assertAstEquals(root1.zero()[i], root2.zero()[i])) {
                    return false;
                }
            }
        }
        if (root1.one() != null) {
            for (int i = 0; i < root1.one().length; i++) {
                if (!assertAstEquals(root1.one()[i], root2.one()[i])) {
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

    static void compareComments(TreeNode root1, TreeNode root2) {
        boolean hasComments1 = root1.getPreComments() != null && root1.getPreComments().length > 0;
        boolean hasComments2 = root2.getPreComments() != null && root2.getPreComments().length > 0;
        assertEquals(hasComments1, hasComments2, "Comments do not match, Node image: " + root1.getHumanReadableImage() + " location: " + root1.getLocation());
        if (hasComments1) {
            assertEquals(root1.getPreComments().length, root2.getPreComments().length);
            for (int i = 0; i < root1.getPreComments().length; i++) {
                assertEquals(root1.getPreComments()[i], root2.getPreComments()[i]);
            }
        }
    }

    /**
     * Helper method to test formatting with idempotency check
     */
    public static void idempotency(String spec) throws IOException, SanyFrontendException {
        // First pass
        TLAPlusFormatter formatter1 = new TLAPlusFormatter(spec);
        String output1 = formatter1.getOutput();
        // Second pass - must be identical
        TLAPlusFormatter formatter2 = new TLAPlusFormatter(output1);
        String output2 = formatter2.getOutput();
        // Verify idempotency
        assertEquals(output1, output2, "Formatter should be idempotent");
        assertTrue(assertAstEquals(formatter1.root, formatter2.root));
    }

    public static void assertSpecEquals(String expected, String input, FormatConfig config) {
        try {
            var f = new TLAPlusFormatter(input, config);
            var received = f.getOutput();
            assertEquals(expected, received, "Formatted output does not match expected output");

        } catch (Exception e) { //  throws FrontEndException, IOException
            fail(e);
        }
        try {
            idempotency(input);
        } catch (Exception e) {
            fail(e);
        }
    }

    /**
     * Verify that formatting the input spec does not change it.
     * Idempotency is also checked.
     *
     * @param input
     */
    public static void assertSpecUnchanged(String input) {
        assertSpecEquals(input, input, new FormatConfig());
    }

    public static void assertSpecEquals(String expected, String input) {
        assertSpecEquals(expected, input, new FormatConfig());
    }

    public static void assertSpecEquals(String expected, String input, int lineWidth) {
        assertSpecEquals(expected, input, new FormatConfig(lineWidth, FormatConfig.DEFAULT_INDENT_SIZE));
    }
}
