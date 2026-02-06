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
