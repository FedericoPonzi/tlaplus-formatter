package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.LexiconTest;
import org.junit.jupiter.api.Test;

public class VariablesTest extends LexiconTest {
    @Test
    public void testFormatVariables() {
        var spec = "----- MODULE Spec -----\n" +
                "\n" +
                "VARIABLES x, y\n" +
                "\n" +
                "====\n";

        var expected = "----- MODULE Spec -----\n" +
                "\n" +
                "VARIABLES\n" +
                "          x,\n" +
                "          y\n" +
                "\n" +
                "====\n";
        assertSpecEquals(expected, spec);
    }
}
