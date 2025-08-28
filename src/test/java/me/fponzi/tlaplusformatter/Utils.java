package me.fponzi.tlaplusformatter;

import me.fponzi.tlaplusformatter.exceptions.SanyFrontendException;

import java.io.IOException;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class Utils {

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
}
