package me.fponzi.tlaplusformatter.constructs.impl;

import org.junit.jupiter.api.Test;

import static me.fponzi.tlaplusformatter.Utils.assertSpecEquals;
import static me.fponzi.tlaplusformatter.Utils.assertUnchanged;

class MaybeBoundConstructTest {
    @Test
    void testCompact() {
        var s = "----- MODULE MaybeBound -----\n" +
                "CONSTANT S\n" +
                "Test == CHOOSE e \\in S : TRUE\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    void testWrapped() {
        var t = "AVeryLongTestName == CHOOSE AVeryLongConstantName \\in AVeryLongConstantNameThatForcesWrapping : TRUE";
        var s = "----- MODULE MaybeBound -----\n" +
                "CONSTANT AVeryLongConstantNameThatForcesWrapping\n" +
                t + "\n" +
                "====";
        var expected = "----- MODULE MaybeBound -----\n" +
                "CONSTANT AVeryLongConstantNameThatForcesWrapping\n" +
                "AVeryLongTestName ==\n" +
                "  CHOOSE AVeryLongConstantName \\in\n" +
                "    AVeryLongConstantNameThatForcesWrapping : TRUE\n" +
                "====";

        assertSpecEquals(expected, s, t.length() / 2);
    }
}