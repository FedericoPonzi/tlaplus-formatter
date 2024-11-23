package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.LexiconTest;
import org.junit.jupiter.api.Test;

public class IfThenElseTest extends LexiconTest {
    @Test
    void testFormatIfThenElseConjDisjList() {
        var spec = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals\n" +
                "CONSTANTS\n" +
                "  Prisoner,\n" +
                "  Counter\n" +
                "VARIABLES\n" +
                "  switchAUp, switchBUp,\n" +
                "  timesSwitched,\n" +
                "  count\n" +
                "\n" +
                "CounterStep ==\n" +
                "  /\\ IF switchAUp\n" +
                "       THEN /\\ switchAUp' = FALSE\n" +
                "            /\\ UNCHANGED switchBUp\n" +
                "            /\\ count' =  count + 1\n" +
                "       ELSE \\/ switchBUp' = ~switchBUp\n" +
                "            \\/ UNCHANGED <<switchAUp, count>>\n" +
                "  /\\ UNCHANGED timesSwitched\n" +
                "\n" +
                "====\n";
        var expected = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals\n" +
                "CONSTANTS\n" +
                "          Prisoner,\n" +
                "          Counter\n" +
                "VARIABLES\n" +
                "          switchAUp,\n" +
                "          switchBUp,\n" +
                "          timesSwitched,\n" +
                "          count\n" +
                "\n" +
                "CounterStep ==\n" +
                "               /\\ IF\n" +
                "                       switchAUp\n" +
                "                  THEN\n" +
                "                       /\\ switchAUp' = FALSE\n" +
                "                       /\\ UNCHANGED switchBUp\n" +
                "                       /\\ count' = count + 1\n" +
                "                  ELSE\n" +
                "                       \\/ switchBUp' = ~switchBUp\n" +
                "                       \\/ UNCHANGED <<switchAUp, count>>\n" +
                "               /\\ UNCHANGED timesSwitched\n" +
                "\n" +
                "====\n";
        // TODO: where did the new line before the ==== go?!?!
        assertSpecEquals(expected, spec);
    }
}
