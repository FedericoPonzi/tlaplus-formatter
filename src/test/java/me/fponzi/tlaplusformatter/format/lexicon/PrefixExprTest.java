package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.SanyTester;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class PrefixExprTest extends SanyTester {

    @Test
    public void testPrefixExpr() {
        // "short" lists are all in the same line
        var spec = "----- MODULE Spec -----\n" +
                "VARIABLES pick, message, sampleSet, loopVariant\n" +
                "Next == UNCHANGED <<pick, message, sampleSet, loopVariant>>\n" +
                "====\n";

        var expected = "----- MODULE Spec -----\n" +
                "\n" +
                "VARIABLES\n" +
                "          pick,\n" +
                "          message,\n" +
                "          sampleSet,\n" +
                "          loopVariant\n" +
                "\n" +
                "Next ==\n" +
                "        UNCHANGED <<pick, message, sampleSet, loopVariant>>\n" +
                "\n" +
                "====\n";

        assertSpecEquals(expected, spec);

        // unless they already broke them on multiple lines:

        spec = "----- MODULE Spec -----\n" +
                "VARIABLES pick, message, sampleSet, loopVariant\n" +
                "Next == UNCHANGED <<pick, message, sampleSet, \n" +
                "loopVariant>>\n" +
                "====\n";

        expected = "----- MODULE Spec -----\n" +
                "\n" +
                "VARIABLES\n" +
                "          pick,\n" +
                "          message,\n" +
                "          sampleSet,\n" +
                "          loopVariant\n" +
                "\n" +
                "Next ==\n" +
                "        UNCHANGED <<\n" +
                "                     pick,\n" +
                "                     message,\n" +
                "                     sampleSet,\n" +
                "                     loopVariant\n" +
                "                   >>\n" +
                "\n" +
                "====\n";

        assertSpecEquals(expected, spec);


    }
}