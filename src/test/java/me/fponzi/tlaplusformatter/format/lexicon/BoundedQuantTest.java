package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.LexiconTest;
import org.junit.jupiter.api.Test;

public class BoundedQuantTest extends LexiconTest {

    @Test
    public void testBoundedQuant() {
        var spec = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals, Sequences\n" +
                "CONSTANT max\n" +
                "S == \\A a \\in 1..max: \\E b \\in 1..max: a < b \n" +
                "====\n";
        var expected = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals, Sequences\n" +
                "CONSTANT\n" +
                "         max\n" +
                "S ==\n" +
                "     \\A a \\in 1 .. max: \\E b \\in 1 .. max: a < b\n" +
                "====\n";
        assertSpecEquals(expected, spec);
    }

}
