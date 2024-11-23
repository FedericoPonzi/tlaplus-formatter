package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.LexiconTest;
import org.junit.jupiter.api.Test;

public class SubsetOfTest extends LexiconTest {
    @Test
    public void testSubsetOf() {
        var spec = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals, Sequences\n" +
                "CONSTANT max\n" +
                "S ==\n" +
                " { x \\in 1 .. max: x < max}\n" +
                "====\n";
        var expected = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals, Sequences\n" +
                "CONSTANT\n" +
                "         max\n" +
                "S ==\n" +
                "     { x \\in 1 .. max: x < max }\n" +
                "====\n";
        assertSpecEquals(expected, spec);
    }
}
