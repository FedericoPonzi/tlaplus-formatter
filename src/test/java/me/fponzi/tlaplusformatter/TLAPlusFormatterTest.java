package me.fponzi.tlaplusformatter;

import org.junit.jupiter.api.Test;
import tla2sany.drivers.FrontEndException;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

class TLAPlusFormatterTest {

    @Test
    void format() throws URISyntaxException, IOException, FrontEndException {
        //load file test/resources/inputs/HourClock.tla
        // format
        // compare to test/resources/outputs/HourClock.tla
        // Get the resource as a URL
        URL resource = getClass().getClassLoader().getResource("inputs/HourClock.tla");
        assertNotNull(resource, "Resource file not found");
        File input = new File(resource.toURI());

        URL outputFile = getClass().getClassLoader().getResource("outputs/HourClock.tla");
        assertNotNull(resource, "Resource file not found");
        System.out.println(outputFile);
        String expected = Files.readString(Path.of(outputFile.toURI()));
        System.out.println("Expected: " + expected);
        var f = new TLAPlusFormatter(input);
        var actual = f.getOutput();
        assertNotNull(actual, "Formatted output is null");
        assertNotNull(expected, "Expected output is null");
        assertEquals(expected, actual, "Formatted output does not match expected output");
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
    public void testFormatAssume() throws FrontEndException, IOException {
        var spec = "------------------------------ MODULE Spec -----------------------------\n" +
                "EXTENDS Naturals\n" +
                "CONSTANT x\n" +
                "ASSUME x \\in Nat\n" +
                "=============================================================================\n";

        var expected = "------------------------------ MODULE Spec -----------------------------\n" +
                "\n" +
                "EXTENDS Naturals\n\n"+
                "CONSTANT\n" +
                "         x\n" +
                "ASSUME\n" +
                "       x \\in Nat \n" +
                "\n" +
                "=============================================================================\n";
        var f = new TLAPlusFormatter(spec);
        var received = f.getOutput();
        assertEquals(expected, received, "Formatted output does not match expected output");
    }

    @Test
    void testFormatIfThenElseConjList() throws FrontEndException, IOException {
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
                "       ELSE /\\ switchBUp' = ~switchBUp\n" +
                "            /\\ UNCHANGED <<switchAUp, count>>\n" +
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
                "                       switchAUp \n" +
                "                  THEN\n" +
                "                       /\\ switchAUp' = FALSE \n" +
                "                       /\\ UNCHANGED switchBUp \n" +
                "                       /\\ count' = count + 1 \n" +
                "                  ELSE\n" +
                "                       /\\ switchBUp' = ~ switchBUp \n" +
                "                       /\\ UNCHANGED << switchAUp , count >> \n" +
                "               /\\ UNCHANGED timesSwitched \n" +
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
                "               1 \n" +
                "          b ==\n" +
                "               2 \n" +
                "      IN \n" +
                "          10 \n" +
                "\n" +
                "=============================================================================\n";
        var f = new TLAPlusFormatter(spec);
        var received = f.getOutput();
        assertEquals(expected, received, "Formatted output does not match expected output");
    }

}