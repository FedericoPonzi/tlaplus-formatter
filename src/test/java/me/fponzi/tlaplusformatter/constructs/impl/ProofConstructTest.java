package me.fponzi.tlaplusformatter.constructs.impl;

import org.junit.jupiter.api.Test;

import static me.fponzi.tlaplusformatter.Utils.assertSpecEquals;
import static me.fponzi.tlaplusformatter.Utils.assertUnchanged;

public class ProofConstructTest {

    @Test
    void testSimpleProof() {
        var s = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "VARIABLE x\n" +
                "THEOREM x = x\n" +
                "<1>1. x = x OBVIOUS\n" +
                "<1>. QED BY <1>1\n" +
                "====";
        assertUnchanged(s);
    }

    @Test
    void testNestedProofSteps() {
        var input = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "VARIABLE x\n" +
                "THEOREM x = x\n" +
                "<1>1. x = x\n" +
                "  <2>1. x = x\n" +
                "    OBVIOUS\n" +
                "  <2>. QED BY <2>1\n" +
                "<1>. QED BY <1>1\n" +
                "====";
        var expected = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "VARIABLE x\n" +
                "THEOREM x = x\n" +
                "<1>1. x = x\n" +
                "  <2>1. x = x OBVIOUS\n" +
                "  <2>. QED BY <2>1\n" +
                "<1>. QED BY <1>1\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    void testProofWithBY() {
        var input = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "VARIABLE x\n" +
                "THEOREM x = x OBVIOUS\n" +
                "====";
        var expected = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "VARIABLE x\n" +
                "THEOREM x = x\n" +
                "OBVIOUS\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    void testBlockCommentBeforeBY() {
        // Pattern from ReachabilityProofs.tla: block comment before BY keyword
        var input = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "VARIABLE x\n" +
                "THEOREM x = x\n" +
                "<1>1. x = x\n" +
                "  (**************)\n" +
                "  (* A comment. *)\n" +
                "  (**************)\n" +
                "  OBVIOUS\n" +
                "<1>. QED BY <1>1\n" +
                "====";
        assertUnchanged(input);
    }

    @Test
    void testLineCommentBeforeBY() {
        // Line comment before BY keyword in proof step
        var input = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "VARIABLE x\n" +
                "THEOREM x = x\n" +
                "<1>1. x = x\n" +
                "  \\* This step is obvious.\n" +
                "  OBVIOUS\n" +
                "<1>. QED BY <1>1\n" +
                "====";
        assertUnchanged(input);
    }

    @Test
    void testBlockCommentBeforeOBVIOUS() {
        // Block comment before OBVIOUS keyword in proof step
        var input = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "VARIABLE x\n" +
                "THEOREM x = x\n" +
                "<1>1. x = x\n" +
                "  (* This is trivial. *)\n" +
                "  OBVIOUS\n" +
                "<1>. QED BY <1>1\n" +
                "====";
        assertUnchanged(input);
    }

    @Test
    void testLineCommentBeforeBYWithRef() {
        // Line comment before BY <ref> in terminal proof
        var input = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "VARIABLE x\n" +
                "THEOREM x = x\n" +
                "<1>1. x = x OBVIOUS\n" +
                "<1>. QED\n" +
                "  \\* Use the step above.\n" +
                "  BY <1>1\n" +
                "====";
        assertUnchanged(input);
    }

    @Test
    void testCommentInNestedProofBeforeBY() {
        // Comment before BY/OBVIOUS in nested proof steps (multiple levels)
        var input = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "VARIABLE x\n" +
                "THEOREM x = x\n" +
                "<1>1. x = x\n" +
                "  <2>1. x = x\n" +
                "    \\* Nested proof comment.\n" +
                "    OBVIOUS\n" +
                "  <2>. QED\n" +
                "    \\* QED is simple.\n" +
                "    BY <2>1\n" +
                "<1>. QED BY <1>1\n" +
                "====";
        assertUnchanged(input);
    }

    @Test
    void testProofWithSuffices() {
        var input = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "CONSTANT S\n" +
                "THEOREM S = S\n" +
                "<1>. SUFFICES ASSUME S = S\n" +
                "             PROVE S = S\n" +
                "  OBVIOUS\n" +
                "<1>. QED\n" +
                "====";
        var expected = "----- MODULE Test -----\n" +
                "EXTENDS TLAPS\n" +
                "CONSTANT S\n" +
                "THEOREM S = S\n" +
                "<1>. SUFFICES ASSUME S = S PROVE S = S OBVIOUS\n" +
                "<1>. QED\n" +
                "====";
        assertSpecEquals(expected, input);
    }
}
