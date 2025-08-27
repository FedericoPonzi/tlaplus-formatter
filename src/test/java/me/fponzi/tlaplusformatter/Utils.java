package me.fponzi.tlaplusformatter;

import me.fponzi.tlaplusformatter.exceptions.SanyFrontendException;

import java.io.IOException;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class Utils {

    /**
     * Helper method to test formatting with idempotency check
     */
    public static void testFormattingIdempotency(String testName, String spec) throws IOException, SanyFrontendException {
        // First pass
        TLAPlusFormatter formatter1 = new TLAPlusFormatter(spec);
        String output1 = formatter1.getOutput();
        System.out.println("=== " + testName + " FIRST PASS ===");
        System.out.println(output1);

        // Second pass - must be identical
        TLAPlusFormatter formatter2 = new TLAPlusFormatter(output1);
        String output2 = formatter2.getOutput();
        System.out.println("=== " + testName + " SECOND PASS ===");
        System.out.println(output2);

        // Verify idempotency
        assertEquals(output1, output2, "Formatter should be idempotent for " + testName);
    }
}
