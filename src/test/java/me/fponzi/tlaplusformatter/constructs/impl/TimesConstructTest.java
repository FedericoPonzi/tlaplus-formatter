package me.fponzi.tlaplusformatter.constructs.impl;

import me.fponzi.tlaplusformatter.FormatConfig;
import me.fponzi.tlaplusformatter.TLAPlusFormatter;
import me.fponzi.tlaplusformatter.exceptions.SanyFrontendException;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static me.fponzi.tlaplusformatter.Utils.idempotency;
import static org.junit.jupiter.api.Assertions.assertEquals;

class TimesConstructTest {
    @Test
    void testTimesCompact() throws SanyFrontendException, IOException {
        var s = "----- MODULE Times -----\n" +
                "CONSTANTS A, B\n" +
                "AVeryLongName == A \\X B\n" +
                "====";

        var f = (new TLAPlusFormatter(s)).getOutput();
        assertEquals(s, f);
        idempotency(s);
    }

    @Test
    void testTimesWrapped() throws SanyFrontendException, IOException {
        var t = "ALongLineName == AVeryLongConstName \\X BVeryLongConstName";
        var s = "----- MODULE Times -----\n" +
                "CONSTANTS AVeryLongConstName, BVeryLongConstName\n" +
                t + "\n" +
                "====";

        var f = (new TLAPlusFormatter(s, new FormatConfig(t.length() / 2, 2))).getOutput();
        var expected = "----- MODULE Times -----\n" +
                "CONSTANTS AVeryLongConstName, BVeryLongConstName\n" +
                "ALongLineName ==\n" +
                "  AVeryLongConstName \\X\n" +
                "    BVeryLongConstName\n" +
                "====";

        assertEquals(expected, f);
        idempotency(s);

    }
}