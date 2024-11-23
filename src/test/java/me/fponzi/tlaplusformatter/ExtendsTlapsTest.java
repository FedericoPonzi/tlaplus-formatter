package me.fponzi.tlaplusformatter;

import org.junit.jupiter.api.Test;

/**
 * Test that EXTENDS TLAPS works. Tlaps is provided as part of the formatter for now.
 */
public class ExtendsTlapsTest extends LexiconTest {

    @Test
    public void testExtendsTlaps() {
        var spec = "----- MODULE Spec -----\n" +
                "EXTENDS TLAPS, Naturals\n" +
                "CONSTANT x\n" +
                "THEOREM x \\in Nat \\land x > 10\n" +
                "====\n";

        var expected = "----- MODULE Spec -----\n" +
                "EXTENDS TLAPS, Naturals\n" +
                "CONSTANT\n" +
                "         x\n" +
                "THEOREM\n" +
                "        x \\in Nat \\land x > 10\n" +
                "====\n";
        assertSpecEquals(expected, spec);
    }
}
