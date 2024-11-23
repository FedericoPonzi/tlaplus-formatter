package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.LexiconTest;
import org.junit.jupiter.api.Test;

public class SetOfAllTest extends LexiconTest {
    @Test
    public void testSetOfAllMultipleQuantifiers() {
        var spec = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals, Sequences\n" +
                "CONSTANT a\n" +
                " RecordCombine(S, T) ==\n" +
                "   {a : s \\in S, t \\in T}\n" +
                "====\n";
        var expected = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals, Sequences\n" +
                "CONSTANT\n" +
                "         a\n" +
                "RecordCombine(S, T) ==\n" +
                "                       {a: s \\in S, t \\in T}\n" +
                "====\n";
        assertSpecEquals(expected, spec);
    }
}
