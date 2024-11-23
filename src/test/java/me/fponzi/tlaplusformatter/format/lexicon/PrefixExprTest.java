package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.LexiconTest;
import org.junit.jupiter.api.Test;

class PrefixExprTest extends LexiconTest {
    @Test
    public void testPrefixEpr2() {
        var spec = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals, Sequences\n" +
                "CONSTANT Proc, pc\n" +
                "AgrrLtl ==\n" +
                "  [](~(\\E i \\in Proc, j \\in Proc :  pc[i] = \"COMMIT\" /\\ pc[j] = \"ABORT\"))\n" +
                "====\n";
        var expected = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals, Sequences\n" +
                "CONSTANT\n" +
                "         Proc,\n" +
                "         pc\n" +
                "AgrrLtl ==\n" +
                "           [](~(\\E i \\in Proc, j \\in Proc: pc[i] = \"COMMIT\" /\\ pc[j] = \"ABORT\"))\n" +
                "====\n";
        assertSpecEquals(expected, spec);
    }


    @Test
    public void testPrefixExpr() {
        // "short" lists are all in the same line
        var spec = "----- MODULE Spec -----\n" +
                "VARIABLES pick, message, sampleSet, loopVariant\n" +
                "Next == UNCHANGED <<pick, message, sampleSet, loopVariant>>\n" +
                "====\n";

        var expected = "----- MODULE Spec -----\n" +
                "VARIABLES\n" +
                "          pick,\n" +
                "          message,\n" +
                "          sampleSet,\n" +
                "          loopVariant\n" +
                "Next ==\n" +
                "        UNCHANGED <<pick, message, sampleSet, loopVariant>>\n" +
                "====\n";

        assertSpecEquals(expected, spec);

        // unless they already broke them on multiple lines:

        spec = "----- MODULE Spec -----\n" +
                "VARIABLES pick, message, sampleSet, loopVariant\n" +
                "Next == UNCHANGED <<pick, message, sampleSet, \n" +
                "loopVariant>>\n" +
                "====\n";

        expected = "----- MODULE Spec -----\n" +
                "VARIABLES\n" +
                "          pick,\n" +
                "          message,\n" +
                "          sampleSet,\n" +
                "          loopVariant\n" +
                "Next ==\n" +
                "        UNCHANGED <<\n" +
                "                     pick,\n" +
                "                     message,\n" +
                "                     sampleSet,\n" +
                "                     loopVariant\n" +
                "                   >>\n" +
                "====\n";

        assertSpecEquals(expected, spec);


    }
}