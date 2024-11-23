package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.LexiconTest;
import org.junit.jupiter.api.Test;

public class LetInTest extends LexiconTest {
    @Test
    public void testLetIn() {
        var spec = "----- MODULE Spec -----\n" +
                "MH == LET x == 1\n" +
                "          b == 2 IN 10\n" +
                "====\n";

        var expected = "----- MODULE Spec -----\n" +
                "MH ==\n" +
                "      LET\n" +
                "          x ==\n" +
                "               1\n" +
                "          b ==\n" +
                "               2\n" +
                "      IN\n" +
                "          10\n" +
                "====\n";
        assertSpecEquals(expected, spec);
    }
}
