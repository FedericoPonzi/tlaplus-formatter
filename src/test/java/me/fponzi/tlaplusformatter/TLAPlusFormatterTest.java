package me.fponzi.tlaplusformatter;

import org.junit.jupiter.api.Test;

class TLAPlusFormatterTest extends LexiconTest {

    @Test
    public void testPlayground() {
        var spec = "----- MODULE Spec -----\n" +
                "EXTENDS TLC, Sequences\n" +
                "CONSTANTS n1, n2, n3\n" +
                "Next == <<1, [counter |-> (n1 :> (n1 :> 0 @@ n2 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 0))]>>\n" +
                "====\n";

        var expected = "----- MODULE Spec -----\n" +
                "EXTENDS TLC, Sequences\n" +
                "CONSTANTS\n" +
                "          n1,\n" +
                "          n2,\n" +
                "          n3\n" +
                "Next ==\n" +
                "        <<\n" +
                "           1,\n" +
                "           [\n" +
                "             counter |-> (n1 :> (n1 :> 0 @@ n2 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 0))\n" +
                "           ]\n" +
                "        >>\n" +
                "====\n";

        assertSpecEquals(expected, spec);
    }

    @Test
    void testFormatHourClock() {
        testSpecFiles("HourClock");
    }

    @Test
    void testFormatComplex() {
        testSpecFiles("RecordsWithNestedRecordsAndSequences");
    }

    @Test
    void testFormatStones() {
        testSpecFiles("Stones");
    }

    @Test
    void testFormatTowerOfHanoi() {
        testSpecFiles("TowerOfHanoi");
    }

    @Test
    void testFormatTransitiveClosure() {
        testSpecFiles("TransitiveClosure");
    }

    @Test
    void testFormatSpanning() {
        // TODO: for some reason at the end there is a \n==== instead of \n\n===== (check input file)
        testSpecFiles("spanning");
    }

    @Test
    void testFormatSlush() {
        testSpecFiles("Slush");
    }

    @Test
    void testSubmodules(){testSpecFiles("Submodules");}

    @Test
    public void testInstance() {
        var spec = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals, Sequences\n" +
                "CONSTANT a\n" +
                "N == INSTANCE Naturals\n" +
                "\n" +
                "UndefinedHashesExist == N!Nat\n" +
                "====\n";
        var expected = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals, Sequences\n" +
                "CONSTANT\n" +
                "         a\n" +
                "N ==\n" +
                "     INSTANCE Naturals\n" +
                "\n" +
                "UndefinedHashesExist ==\n" +
                "                        N!Nat\n" +
                "====\n";
        assertSpecEquals(expected, spec);
    }

    @Test
    public void testInstanceWith() {
        var spec2 = "----- MODULE Spec2 -----\n" +
                "CONSTANT pc, vroot\n" +
                "====\n";
        var spec = "----- MODULE Spec -----\n" +
                "\n" +
                "CONSTANT vrootBar, pcBar\n" +
                "N == INSTANCE Spec2 WITH vroot <- vrootBar, pc <- pcBar\n" +
                "====\n";
        var expected = "----- MODULE Spec -----\n" +
                "\n" +
                "CONSTANT\n" +
                "         vrootBar,\n" +
                "         pcBar\n" +
                "N ==\n" +
                "     INSTANCE Spec2 WITH vroot <- vrootBar,\n" +
                "                         pc <- pcBar\n" +
                "====\n";

        assertSpecEquals(expected, spec, spec2);
    }


    // TODO: test choose, also test:
    /* CHOOSE bc \in (Ballots \X Commands): /\ \E pr \in prs: /\ pr.votes[s].bal = bc[1]
                                                                                              /\ pr.votes[s].cmd = bc[2]
                                                                            /\ \A pr \in prs: pr.votes[s].bal =< bc[1]
     */

}

