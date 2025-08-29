package me.fponzi.tlaplusformatter.constructs.impl;

import org.junit.jupiter.api.Test;

import static me.fponzi.tlaplusformatter.Utils.assertSpecEquals;
import static me.fponzi.tlaplusformatter.Utils.assertUnchanged;

class IfThenElseConstructTest {
    @Test
    void testCompact() {
        var s = "----- MODULE Times -----\n" +
                "CONSTANTS A, B\n" +
                "AVeryLongName == IF TRUE THEN A ELSE B\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    void testWrapped() {

        var t = "ALongLineName == IF TRUE THEN AVeryLongConstName ELSE BVeryLongConstName";
        var s = "----- MODULE Times -----\n" +
                "CONSTANTS AVeryLongConstName, BVeryLongConstName\n" +
                t + "\n" +
                "====";
        var expected = "----- MODULE Times -----\n" +
                "CONSTANTS AVeryLongConstName, BVeryLongConstName\n" +
                "ALongLineName ==\n" +
                "  IF TRUE\n" +
                "  THEN AVeryLongConstName\n" +
                "  ELSE BVeryLongConstName\n" +
                "====";

        assertSpecEquals(expected, s, t.length() / 2);
    }

}