package me.fponzi.tlaplusformatter;

import org.junit.jupiter.api.Test;
import tla2sany.drivers.FrontEndException;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.*;

class TLAPlusFormatterTest {

    /**
     * Compares src/test/resources/inputs/name.tla to src/test/resources/outputs/name.tla
     */
    void testSpecFiles(String name) {
        try {
            URL resource = getClass().getClassLoader().getResource("inputs/" + name + ".tla");
            assertNotNull(resource, "Resource file not found");
            File input = new File(resource.toURI());

            URL outputFile = getClass().getClassLoader().getResource("outputs/" + name + ".tla");
            assertNotNull(resource, "Resource file not found");
            String expected = Files.readString(Path.of(outputFile.toURI()));
            var f = new TLAPlusFormatter(input);
            var actual = f.getOutput();
            assertNotNull(actual, "Formatted output is null");
            assertNotNull(expected, "Expected output is null");
            assertEquals(expected, actual, "Formatted output does not match expected output");
            // here we use the downside of having SANY validating the spec
            // as an advantage to ensure the specs are valid.
            // also, the formatting should be stable.
            try {
                // initialize tlaplusfmt using output file path.
                // in this way, if the spec EXTENDS other specs, we can include them in the outputs resource folder.
                // For example see TowerOfHanoi.tla.
                f = new TLAPlusFormatter(new File(outputFile.toURI()));
                actual = f.getOutput();
                assertNotNull(actual, "Formatted output is null");
                assertEquals(expected, actual, "Second formatted output does not match expected output");
            } catch (Exception e) {
                fail(actual, e);
            }

        } catch (Exception e){
            fail(e);
        }
    }


    @Test
    void testFormatHourClock() {
        testSpecFiles("HourClock");
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
        testSpecFiles("spanning");
    }

    @Test
    void testFormatSlush() {
        testSpecFiles("Slush");
    }

    @Test
    void testFormatModule() throws FrontEndException, IOException {
        var spec = "---- MODULE Spec ----\n======";
        var expected = "---- MODULE Spec ----\n\n======\n";
        var f = new TLAPlusFormatter(spec);
        var received = f.getOutput();
        assertEquals(expected, received, "Formatted output does not match expected output");
    }

    @Test
    void testFormatModule2() throws FrontEndException, IOException {
        var spec = "---- MODULE Spec ----\n\n======";
        var expected = "---- MODULE Spec ----\n\n======\n";
        var f = new TLAPlusFormatter(spec);
        var received = f.getOutput();
        assertEquals(expected, received, "Formatted output does not match expected output");
    }

    @Test
    void testFormatExtends() throws FrontEndException, IOException {
        var spec = "---- MODULE Spec ----\nEXTENDS Naturals\n======";
        var expected = "---- MODULE Spec ----\n\nEXTENDS Naturals\n\n======\n";
        var f = new TLAPlusFormatter(spec);
        var received = f.getOutput();
        assertEquals(expected, received, "Formatted output does not match expected output");
    }

    @Test
    public void testFormatVariables() throws FrontEndException, IOException {
        var spec = "------------------------------ MODULE Spec -----------------------------\n" +
                "VARIABLES x, y\n" +
                "=============================================================================\n";

        var expected = "------------------------------ MODULE Spec -----------------------------\n" +
                "\n" +
                "VARIABLES\n" +
                "          x,\n" +
                "          y\n" +
                "\n" +
                "=============================================================================\n";
        var f = new TLAPlusFormatter(spec);
        var received = f.getOutput();
        assertEquals(expected, received, "Formatted output does not match expected output");
    }
    @Test
    public void testConstants() throws FrontEndException, IOException {
        // using Constants
        var spec = "------------------------------ MODULE Spec -----------------------------\n" +
                "CONSTANTS x, y\n" +
                "=============================================================================\n";
        var expected = "------------------------------ MODULE Spec -----------------------------\n" +
                "\n" +
                "CONSTANTS\n" +
                "          x,\n" +
                "          y\n" +
                "=============================================================================\n";
        var f = new TLAPlusFormatter(spec);
        var received = f.getOutput();
        assertEquals(expected, received, "Formatted output does not match expected output");
    }
    @Test
    public void testConstantsParamsIdentDecl() throws FrontEndException, IOException {
        // using Constants
        var spec = "------------------------------ MODULE Spec -----------------------------\n" +
                "CONSTANTS  CalculateHash(_,_,_)\n" +
                "=============================================================================\n";
        var expected = "------------------------------ MODULE Spec -----------------------------\n" +
                "\n" +
                "CONSTANTS\n" +
                "          CalculateHash(_,_,_)\n" +
                "=============================================================================\n";
        var f = new TLAPlusFormatter(spec);
        var received = f.getOutput();
        assertEquals(expected, received, "Formatted output does not match expected output");
    }
    @Test
    public void testFormatAssume() throws FrontEndException, IOException {
        var spec = "------------------------------ MODULE Spec -----------------------------\n" +
                "EXTENDS Naturals\n" +
                "CONSTANT x\n" +
                "ASSUME x \\in Nat\n" +
                "=============================================================================\n";

        var expected = "------------------------------ MODULE Spec -----------------------------\n" +
                "\n" +
                "EXTENDS Naturals\n\n" +
                "CONSTANT\n" +
                "         x\n" +
                "ASSUME\n" +
                "       x \\in Nat\n" +
                "\n" +
                "=============================================================================\n";
        var f = new TLAPlusFormatter(spec);
        var received = f.getOutput();
        assertEquals(expected, received, "Formatted output does not match expected output");
    }

    @Test
    public void testFormatAssumeConjList() throws FrontEndException, IOException {
        var spec = "------------------------------ MODULE Spec -----------------------------\n" +
                "EXTENDS Naturals\n" +
                "CONSTANT x\n" +
                "ASSUME /\\ x \\in Nat\n" +
                "       /\\ x > 10\n" +
                "=============================================================================\n";

        var expected = "------------------------------ MODULE Spec -----------------------------\n" +
                "\n" +
                "EXTENDS Naturals\n\n" +
                "CONSTANT\n" +
                "         x\n" +
                "ASSUME\n" +
                "       /\\ x \\in Nat\n" +
                "       /\\ x > 10\n" +
                "\n" +
                "=============================================================================\n";
        var f = new TLAPlusFormatter(spec);
        var received = f.getOutput();
        assertEquals(expected, received, "Formatted output does not match expected output");
    }

    @Test
    void testFormatIfThenElseConjDisjList() throws FrontEndException, IOException {
        var spec = "------------------------------ MODULE Spec -----------------------------\n" +
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
                "=============================================================================\n";
        var expected = "------------------------------ MODULE Spec -----------------------------\n" +
                "\n" +
                "EXTENDS Naturals\n" +
                "\n" +
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
                "=============================================================================\n";
        var f = new TLAPlusFormatter(spec);
        var received = f.getOutput();
        assertEquals(expected, received, "Formatted output does not match expected output");
    }

    @Test
    public void testLetIn() throws FrontEndException, IOException {
        var spec = "------------------------------ MODULE Spec -----------------------------\n" +
                "MH == LET x == 1\n" +
                "          b == 2 IN 10" +
                "=============================================================================\n";

        var expected = "------------------------------ MODULE Spec -----------------------------\n" +
                "\n" +
                "MH ==\n" +
                "      LET\n" +
                "          x ==\n" +
                "               1\n" +
                "          b ==\n" +
                "               2\n" +
                "      IN\n" +
                "          10\n" +
                "\n" +
                "=============================================================================\n";
        var f = new TLAPlusFormatter(spec);
        var received = f.getOutput();
        assertEquals(expected, received, "Formatted output does not match expected output");
    }

    @Test
    public void testTheorem() throws FrontEndException, IOException {
        var spec = "------------------------------ MODULE Spec -----------------------------\n" +
                "EXTENDS Naturals\n" +
                "CONSTANT x\n" +
                "THEOREM x \\in Nat \\land x > 10\n" +
                "=============================================================================\n";

        var expected = "------------------------------ MODULE Spec -----------------------------\n\n" +
                "EXTENDS Naturals\n" +
                "\n" +
                "CONSTANT\n" +
                "         x\n" +
                "THEOREM\n" +
                "        x \\in Nat \\land x > 10\n" +
                "=============================================================================\n";
        var f = new TLAPlusFormatter(spec);
        var received = f.getOutput();
        assertEquals(expected, received, "Formatted output does not match expected output");
    }
    @Test
    public void testTheoremAssign() throws FrontEndException, IOException {
        var spec = "------------------------------ MODULE Spec -----------------------------\n" +
                "CONSTANT TypeInvariant, Spec\n" +
                "THEOREM Safety == Spec => TypeInvariant\n\n" +
                "=============================================================================\n";

        // TODO: (safety==Spec)
        var expected = "------------------------------ MODULE Spec -----------------------------\n" +
                "\n" +
                "CONSTANT\n" +
                "         TypeInvariant,\n" +
                "         Spec\n" +
                "THEOREM\n" +
                "        Safety==Spec => TypeInvariant\n"+
                "=============================================================================\n";
        var f = new TLAPlusFormatter(spec);
        var received = f.getOutput();
        assertEquals(expected, received, "Formatted output does not match expected output");
    }

    @Test
    public void testRecursive() throws FrontEndException, IOException {
        var spec = "------------------------------ MODULE Spec -----------------------------\n" +
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
                "         IN UNION { Partitions(<<x>> \\o seq, wt - x ) : x \\in S }\n"+
                "=============================================================================\n";

        var expected = "------------------------------ MODULE Spec -----------------------------\n" +
                "\n" +
                "EXTENDS Naturals, Sequences\n" +
                "\n" +
                "CONSTANT\n" +
                "         N\n" +
                "VARIABLE\n" +
                "         y\n" +
                "\n" +
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
                "\n" +
                "=============================================================================\n";
        var f = new TLAPlusFormatter(spec);
        var received = f.getOutput();
        assertEquals(expected, received, "Formatted output does not match expected output");
    }

    @Test
    public void testSubsetOf() throws FrontEndException, IOException {
        var spec = "------------------------------ MODULE Spec -----------------------------\n" +
                "EXTENDS Naturals, Sequences\n" +
                "CONSTANT max\n" +
                "S ==\n" +
                " { x \\in 1 .. max: x < max}\n" +
                "=============================================================================\n";
        var expected = "------------------------------ MODULE Spec -----------------------------\n" +
                "\n" +
                "EXTENDS Naturals, Sequences\n" +
                "\n" +
                "CONSTANT\n" +
                "         max\n" +
                "S ==\n" +
                "     { x \\in 1 .. max: x < max }\n" +
                "\n" +
                "=============================================================================\n";
        var f = new TLAPlusFormatter(spec);
        var received = f.getOutput();
        assertEquals(expected, received, "Formatted output does not match expected output");
    }
    @Test
    public void testBoundedQuant() throws FrontEndException, IOException {
        var spec = "------------------------------ MODULE Spec -----------------------------\n" +
                "EXTENDS Naturals, Sequences\n" +
                "CONSTANT max\n" +
                "S == \\A a \\in 1..max: \\E b \\in 1..max: a < b \n" +
                "=============================================================================\n";
        var expected = "------------------------------ MODULE Spec -----------------------------\n" +
                "\n" +
                "EXTENDS Naturals, Sequences\n" +
                "\n" +
                "CONSTANT\n" +
                "         max\n" +
                "S ==\n" +
                "     \\A a \\in 1 .. max: \\E b \\in 1 .. max: a < b\n" +
                "\n" +
                "=============================================================================\n";
        var f = new TLAPlusFormatter(spec);
        var received = f.getOutput();
        assertEquals(expected, received, "Formatted output does not match expected output");
    }

    @Test
    public void testDisjList() throws FrontEndException, IOException {
        var spec = "------------------------------ MODULE Spec -----------------------------\n" +
                "EXTENDS Naturals, Sequences\n" +
                "CONSTANT max, wt, r\n" +
                "S == {x \\in 1..max : /\\ (r-1) =< (wt - x)\n" +
                "                                  /\\ wt =< x*r          }" +
                "=============================================================================\n";
        var expected = "------------------------------ MODULE Spec -----------------------------\n" +
                "\n" +
                "EXTENDS Naturals, Sequences\n" +
                "\n" +
                "CONSTANT\n" +
                "         max,\n" +
                "         wt,\n" +
                "         r\n" +
                "S ==\n" +
                "     { x \\in 1 .. max: /\\ (r - 1) =< (wt - x) /\\ wt =< x * r }\n" +
                "\n" +
                "=============================================================================\n";
        var f = new TLAPlusFormatter(spec);
        var received = f.getOutput();
        assertEquals(expected, received, "Formatted output does not match expected output");
        f = new TLAPlusFormatter(received);
        received = f.getOutput();
        assertEquals(expected, received, "Formatted output does not match expected second output");
    }

    @Test
    public void testFcnApplExcept() throws FrontEndException, IOException {
        // TODO:
        var spec = "------------------------------ MODULE Spec -----------------------------\n" +
                "EXTENDS Naturals, Sequences\n" +
                "VARIABLE towers\n" +
                "Move(from, to, disk) ==  towers' = [towers EXCEPT ![from] = towers[from] - disk,  \\* Remaining tower does not change\n" +
                "                                                    ![to] = towers[to] + disk]\n" +
                "=============================================================================\n";
        var expected = "------------------------------ MODULE Spec -----------------------------\n" +
                "\n" +
                "EXTENDS Naturals, Sequences\n" +
                "\n" +
                "VARIABLE\n" +
                "         towers\n" +
                "\n" +
                "Move(from, to, disk) ==\n" +
                "                        towers' = [towers EXCEPT ![from]=towers[from] - disk,\n" +
                "                                                 \\* Remaining tower does not change\n" +
                "                                                 ![to]=towers[to] + disk]\n" +
                "\n" +
                "=============================================================================\n";
        var f = new TLAPlusFormatter(spec);
        var received = f.getOutput();
        assertEquals(expected, received, "Formatted output does not match expected output");
    }
    @Test
    public void testFnAppl_FnDefinition_IfElse_LetIn() throws FrontEndException, IOException {
        var spec = "------------------------------ MODULE Spec -----------------------------\n" +
                "EXTENDS Naturals, FiniteSets\n" +
                "R(s,v) == 0 \n"+
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
                "=============================================================================\n";
        var expected = "------------------------------ MODULE Spec -----------------------------\n" +
                "\n" +
                "EXTENDS Naturals, FiniteSets\n" +
                "\n" +
                "R(s, v) ==\n" +
                "           0\n" +
                "\n" +
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
                "\n" +
                "=============================================================================\n";
        var f = new TLAPlusFormatter(spec);
        var received = f.getOutput();
        assertEquals(expected, received, "Formatted output does not match expected output");
    }
    @Test
    public void testBound() throws FrontEndException, IOException {
        var spec = "------------------------------ MODULE Spec -----------------------------\n" +
                "EXTENDS Naturals, Sequences\n" +
                "CONSTANT a\n" +
                "Support(x) == 0\n"+
                "R ** T == LET SR == Support(R)\n" +
                "              ST == Support(T)\n" +
                "          IN  {<<r, t>> \\in SR \\X ST :\n" +
                "                \\E s \\in SR \\cap ST : (<<r, s>> \\in R) /\\ (<<s, t>> \\in T)}" +
                "=============================================================================\n";
        var expected = "------------------------------ MODULE Spec -----------------------------\n" +
                "\n" +
                "EXTENDS Naturals, Sequences\n" +
                "\n" +
                "CONSTANT\n" +
                "         a\n" +
                "Support(x) ==\n" +
                "              0\n" +
                "\n" +
                "R**T ==\n" +
                "        LET\n" +
                "            SR ==\n" +
                "                  Support(R)\n" +
                "            ST ==\n" +
                "                  Support(T)\n" +
                "        IN\n" +
                "            { <<r,t>> \\in SR \\X ST: \\E s \\in SR \\cap ST: (<<r, s>> \\in R) /\\ (<<s, t>> \\in T) }\n" +
                "\n" +
                "=============================================================================\n";
        var f = new TLAPlusFormatter(spec);
        var received = f.getOutput();
        assertEquals(expected, received, "Formatted output does not match expected output");
    }

    @Test
    public void testPrefixEpr() throws FrontEndException, IOException {
        var spec = "------------------------------ MODULE Spec -----------------------------\n" +
                "EXTENDS Naturals, Sequences\n" +
                "CONSTANT Proc, pc\n" +
                "AgrrLtl ==\n" +
                "  [](~(\\E i \\in Proc, j \\in Proc :  pc[i] = \"COMMIT\" /\\ pc[j] = \"ABORT\"))\n\n" +
                "=============================================================================\n";
        var expected =  "------------------------------ MODULE Spec -----------------------------\n" +
                "\n" +
                "EXTENDS Naturals, Sequences\n" +
                "\n" +
                "CONSTANT\n" +
                "         Proc,\n" +
                "         pc\n" +
                "AgrrLtl ==\n" +
                "           [](~(\\E i \\in Proc, j \\in Proc: pc[i] = \"COMMIT\" /\\ pc[j] = \"ABORT\"))\n" +
                "\n" +
                "=============================================================================\n";
        var f = new TLAPlusFormatter(spec);
        var received = f.getOutput();
        assertEquals(expected, received, "Formatted output does not match expected output");
    }

    @Test
    public void testInstance() throws FrontEndException, IOException {
        var spec = "------------------------------ MODULE Spec -----------------------------\n" +
                "EXTENDS Naturals, Sequences\n" +
                "CONSTANT a\n" +
                "N == INSTANCE Naturals\n" +
                "\n" +
                "UndefinedHashesExist == N!Nat\n" +
                "=============================================================================\n";
        var expected = "------------------------------ MODULE Spec -----------------------------\n" +
                "\n" +
                "EXTENDS Naturals, Sequences\n" +
                "\n" +
                "CONSTANT\n" +
                "         a\n" +
                "N ==\n" +
                "     INSTANCE Naturals\n" +
                "\n"+
                "UndefinedHashesExist ==\n" +
                "                        N!Nat\n" +
                "\n" +
                "=============================================================================\n";
        var f = new TLAPlusFormatter(spec);
        var received = f.getOutput();
        assertEquals(expected, received, "Formatted output does not match expected output");
    }
    // TODO: test choose, also test:
    /* CHOOSE bc \in (Ballots \X Commands): /\ \E pr \in prs: /\ pr.votes[s].bal = bc[1]
                                                                                              /\ pr.votes[s].cmd = bc[2]
                                                                            /\ \A pr \in prs: pr.votes[s].bal =< bc[1]
     */
}

