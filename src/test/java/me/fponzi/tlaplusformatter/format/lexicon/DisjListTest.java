package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.LexiconTest;
import org.junit.jupiter.api.Test;

public class DisjListTest extends LexiconTest {
    @Test
    public void testDisjList() {
        var spec = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals, Sequences\n" +
                "CONSTANT max, wt, r\n" +
                "S == {x \\in 1..max : /\\ (r-1) =< (wt - x)\n" +
                "                                  /\\ wt =< x*r          }\n" +
                "====\n";
        var expected = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals, Sequences\n" +
                "CONSTANT\n" +
                "         max,\n" +
                "         wt,\n" +
                "         r\n" +
                "S ==\n" +
                "     { x \\in 1 .. max: /\\ (r - 1) =< (wt - x) /\\ wt =< x * r }\n" +
                "====\n";
        assertSpecEquals(expected, spec);
    }
}
