package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.LexiconTest;
import org.junit.jupiter.api.Test;

public class RecursiveTest extends LexiconTest {
    @Test
    public void testRecursive() {
        var spec = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals, Sequences\n" +
                "CONSTANT N\n" +
                "VARIABLE y\n" +
                "RECURSIVE Partitions(_ , _)\n" +
                "Partitions(seq, wt) ==\n" +
                "  IF Len(seq) = N\n" +
                "    THEN {seq}\n" +
                "    ELSE LET r == N - Len(seq)\n" +
                "             max == IF Len(seq) = 0 THEN wt ELSE Head(seq)\n" +
                "             S == {x \\in 1..max : /\\ (r-1) =< (wt - x)\n" +
                "                                  /\\ wt =< x*r          }\n" +
                "         IN UNION { Partitions(<<x>> \\o seq, wt - x ) : x \\in S }\n" +
                "====\n";

        var expected = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals, Sequences\n" +
                "CONSTANT\n" +
                "         N\n" +
                "VARIABLE\n" +
                "         y\n" +
                "RECURSIVE Partitions(_,_)\n" +
                "Partitions(seq, wt) ==\n" +
                "                       IF\n" +
                "                            Len(seq) = N\n" +
                "                       THEN\n" +
                "                            {seq}\n" +
                "                       ELSE\n" +
                "                            LET\n" +
                "                                r ==\n" +
                "                                     N - Len(seq)\n" +
                "                                max ==\n" +
                "                                       IF\n" +
                "                                            Len(seq) = 0\n" +
                "                                       THEN\n" +
                "                                            wt\n" +
                "                                       ELSE\n" +
                "                                            Head(seq)\n" +
                "                                S ==\n" +
                "                                     { x \\in 1 .. max: /\\ (r - 1) =< (wt - x)\n" +
                "                                                       /\\ wt =< x * r }\n" +
                "                            IN\n" +
                "                                UNION {Partitions(<<x>> \\o seq, wt - x): x \\in S}\n" +
                "====\n";
        assertSpecEquals(expected, spec);
    }
}
