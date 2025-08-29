package me.fponzi.tlaplusformatter.constructs.impl;

import org.junit.jupiter.api.Test;

import static me.fponzi.tlaplusformatter.Utils.assertSpecEquals;
import static me.fponzi.tlaplusformatter.Utils.assertUnchanged;

class InfixExprConstructTest {
    @Test
    void testCompact() {
        var s = "----- MODULE InfixExpr -----\n" +
                "CONSTANTS S, Z\n" +
                "Test == S \\in Z\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    void testWrapped() {
        var t = "AVeryLongTestName == AVeryLongConstantName \\in AVeryLongConstantNameThatForcesWrapping";
        var s = "----- MODULE InfixExpr -----\n" +
                "CONSTANT AVeryLongConstantName, AVeryLongConstantNameThatForcesWrapping\n" +
                t + "\n" +
                "====";
        var expected = "----- MODULE InfixExpr -----\n" +
                "CONSTANTS AVeryLongConstantName, AVeryLongConstantNameThatForcesWrapping\n" +
                "AVeryLongTestName ==\n" +
                "  AVeryLongConstantName \\in\n" +
                "    AVeryLongConstantNameThatForcesWrapping\n" +
                "====";

        assertSpecEquals(expected, s, t.length() / 2);
    }
}