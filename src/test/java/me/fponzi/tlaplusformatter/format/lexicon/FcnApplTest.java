package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.LexiconTest;
import org.junit.jupiter.api.Test;

public class FcnApplTest extends LexiconTest {
    @Test
    public void testFcnApplExcept() {
        var spec = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals, Sequences\n" +
                "VARIABLE towers\n" +
                "\n" +
                "Move(from, to, disk) ==  towers' = [towers EXCEPT ![from] = towers[from] - disk,  \\* Remaining tower does not change\n" +
                "                                                    ![to] = towers[to] + disk]\n" +
                "====\n";
        var expected = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals, Sequences\n" +
                "VARIABLE\n" +
                "         towers\n" +
                "\n" +
                "Move(from, to, disk) ==\n" +
                "                        towers' = [towers EXCEPT ![from]=towers[from] - disk,\n" +
                "                                                 \\* Remaining tower does not change\n" +
                "                                                 ![to]=towers[to] + disk]\n" +
                "====\n";
        assertSpecEquals(expected, spec);
    }

    @Test
    public void testFnAppl_FnDefinition_IfElse_LetIn() {
        var spec = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals, FiniteSets\n" +
                "R(s,v) == 0 \n" +
                "L(s,t, S) == LET\n" +
                "               CR[n \\in Nat ,v \\in S ] ==  IF\n" +
                "                                                 n = 0\n" +
                "                                            THEN\n" +
                "                                                  R(s, v)\n" +
                "                                              ELSE\n" +
                "                                                  \\/ CR[n - 1,v]\n" +
                "                                                  \\/ \\E u \\in S : CR[n - 1,u] /\\ R(u, v)\n" +
                "                        IN\n" +
                "                            /\\ s \\in S\n" +
                "                            /\\ t \\in S\n" +
                "                            /\\ CR[Cardinality(S) - 1,t]\n" +
                "====\n";
        var expected = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals, FiniteSets\n" +
                "R(s, v) ==\n" +
                "           0\n" +
                "L(s, t, S) ==\n" +
                "              LET\n" +
                "                  CR[n \\in Nat, v \\in S] == IF\n" + // escape chars disalign the vertical align in this view
                "                                                 n = 0\n" +
                "                                            THEN\n" +
                "                                                 R(s, v)\n" +
                "                                            ELSE\n" +
                "                                                 \\/ CR[n - 1, v]\n" +
                "                                                 \\/ \\E u \\in S: CR[n - 1, u] /\\ R(u, v)\n" +
                "              IN\n" +
                "                  /\\ s \\in S\n" +
                "                  /\\ t \\in S\n" +
                "                  /\\ CR[Cardinality(S) - 1, t]\n" +
                "====\n";
        assertSpecEquals(expected, spec);
    }

}
