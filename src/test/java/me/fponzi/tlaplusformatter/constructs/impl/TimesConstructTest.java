package me.fponzi.tlaplusformatter.constructs.impl;

import org.junit.jupiter.api.Test;

import static me.fponzi.tlaplusformatter.Utils.assertSpecEquals;
import static me.fponzi.tlaplusformatter.Utils.assertUnchanged;

class TimesConstructTest {
    @Test
    void testTimesCompact() {
        var s = "----- MODULE Times -----\n" +
                "CONSTANTS A, B\n" +
                "AVeryLongName == A \\X B\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    void testTimesWrapped() {
        var t = "ALongLineName == AVeryLongConstName \\X BVeryLongConstName";
        var s = "----- MODULE Spec -----\n" +
                "CONSTANTS AVeryLongConstName, BVeryLongConstName\n" +
                t + "\n" +
                "====";

        var expected = "----- MODULE Spec -----\n" +
                "CONSTANTS AVeryLongConstName, BVeryLongConstName\n" +
                "ALongLineName ==\n" +
                "  AVeryLongConstName \\X\n" +
                "    BVeryLongConstName\n" +
                "====";
        assertSpecEquals(expected, s, t.length() / 2);
    }
}