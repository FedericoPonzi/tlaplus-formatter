package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.LexiconTest;
import org.junit.jupiter.api.Test;

public class TheoremTest extends LexiconTest {
    @Test
    public void testTheorem() {
        var spec = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals\n" +
                "CONSTANT x\n" +
                "THEOREM x \\in Nat \\land x > 10\n" +
                "====\n";

        var expected = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals\n" +
                "CONSTANT\n" +
                "         x\n" +
                "THEOREM\n" +
                "        x \\in Nat \\land x > 10\n" +
                "====\n";
        assertSpecEquals(expected, spec);
    }

    @Test
    public void testTheoremAssign() {
        var spec = "----- MODULE Spec -----\n" +
                "CONSTANT TypeInvariant, Spec\n" +
                "THEOREM Safety == Spec => TypeInvariant\n" +
                "====\n";

        // TODO: (safety==Spec)
        var expected = "----- MODULE Spec -----\n" +
                "CONSTANT\n" +
                "         TypeInvariant,\n" +
                "         Spec\n" +
                "THEOREM\n" +
                "        Safety==Spec => TypeInvariant\n" +
                "====\n";
        assertSpecEquals(expected, spec);
    }

}
