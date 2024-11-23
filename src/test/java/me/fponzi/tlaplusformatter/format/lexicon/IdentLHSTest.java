package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.LexiconTest;
import org.junit.jupiter.api.Test;

public class IdentLHSTest extends LexiconTest {
    @Test
    void testIdentLHSSimple() {
        var spec = "----- MODULE Spec -----\n" +
                "Move(from, to, disk) == TRUE\n" +
                "====\n";
        var expected = "----- MODULE Spec -----\n" +
                "Move(from, to, disk) ==\n" +
                "                        TRUE\n" +
                "====\n";
        assertSpecEquals(expected, spec);
    }
}
