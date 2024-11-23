package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.LexiconTest;
import org.junit.jupiter.api.Test;

public class OperatorDefinitionTest extends LexiconTest {
    @Test
    public void testOdot() {
        var spec = "----- MODULE Spec -----\n" +
                "EXTENDS Integers\n" +
                "a / b     == IF b /= 0 THEN <<a, b>> ELSE CHOOSE x \\in {} : TRUE\n" +
                "a \\odot b == (a[1]*b[1]) / (a[2]*b[2])\n" +
                "====\n";
        var expected = "----- MODULE Spec -----\n" +
                "EXTENDS Integers\n" +
                "a / b ==\n" +
                "         IF\n" +
                "              b /= 0\n" +
                "         THEN\n" +
                "              <<a, b>>\n" +
                "         ELSE\n" +
                "              CHOOSE x \\in {}: TRUE\n" +
                "a \\odot b ==\n" +
                "             (a[1] * b[1]) / (a[2] * b[2])\n" +
                "====\n";
        assertSpecEquals(expected, spec);
    }
}
