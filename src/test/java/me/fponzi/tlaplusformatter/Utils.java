package me.fponzi.tlaplusformatter;

import me.fponzi.tlaplusformatter.exceptions.SanyFrontendException;

import java.io.IOException;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.fail;

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

    public static void assertSpecEquals(String expected, String input) {
        assertSpecEquals(expected, input, new FormatConfig());
    }

    public static void assertSpecEquals(String expected, String input, int lineWidth) {
        assertSpecEquals(expected, input, new FormatConfig(lineWidth, FormatConfig.DEFAULT_INDENT_SIZE));
    }
}
