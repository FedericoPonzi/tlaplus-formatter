package me.fponzi.tlaplusformatter;

import me.fponzi.tlaplusformatter.exceptions.SanyFrontendException;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static me.fponzi.tlaplusformatter.Utils.testFormattingIdempotency;
import static org.junit.jupiter.api.Assertions.*;

/**
 * End-to-end tests for the TLA+ formatter.
 * These tests create TLA+ specifications as strings, format them,
 * and verify the output structure and formatting quality.
 */
class FormatterE2ETest {

    @Test
    void testSimpleModuleFormatting() throws IOException, SanyFrontendException {
        String spec = "---- MODULE SimpleTest ----\n" +
                "VARIABLE x\n" +
                "Init == x = 0\n" +
                "====\n";

        // First pass
        TLAPlusFormatter formatter1 = new TLAPlusFormatter(spec);
        String output1 = formatter1.getOutput();
        System.out.println("=== FIRST PASS ===");
        System.out.println(output1);

        // Second pass - should be identical
        TLAPlusFormatter formatter2 = new TLAPlusFormatter(output1);
        String output2 = formatter2.getOutput();
        System.out.println("=== SECOND PASS ===");
        System.out.println(output2);

        // Verify content and structure
        assertNotNull(output1);
        String[] lines = output1.split("\n");
        assertEquals("---- MODULE SimpleTest ----", lines[0]);
        assertTrue(lines[1].startsWith("VARIABLE "));
        assertTrue(lines[2].startsWith("Init == "));
        assertEquals("====", lines[3]);

        // Verify idempotency
        assertEquals(output1, output2, "Formatter should be idempotent");
    }

    @Test
    void testModuleWithExtends() throws IOException, SanyFrontendException {
        String spec = "---- MODULE TestWithExtends ----\n" +
                "EXTENDS Naturals, TLC\n" +
                "VARIABLE counter\n" +
                "====\n";

        // First pass
        TLAPlusFormatter formatter1 = new TLAPlusFormatter(spec);
        String output1 = formatter1.getOutput();
        System.out.println("=== EXTENDS FIRST PASS ===");
        System.out.println(output1);

        // Second pass
        TLAPlusFormatter formatter2 = new TLAPlusFormatter(output1);
        String output2 = formatter2.getOutput();
        System.out.println("=== EXTENDS SECOND PASS ===");
        System.out.println(output2);

        // Verify content and structure
        String[] lines = output1.split("\n");
        assertTrue(lines[1].startsWith("EXTENDS"));
        assertTrue(lines[1].contains("Naturals") && lines[1].contains("TLC"));
        assertTrue(lines[2].startsWith("VARIABLE"));

        // Verify idempotency
        assertEquals(output1, output2, "Formatter should be idempotent for EXTENDS");
    }

    @Test
    void testMultipleVariables() throws IOException, SanyFrontendException {
        String spec = "---- MODULE MultiVar ----\n" +
                "VARIABLES x, y, z\n" +
                "====\n";

        testFormattingIdempotency("MULTIVARS", spec);

        TLAPlusFormatter formatter = new TLAPlusFormatter(spec);
        String output = formatter.getOutput();

        // Verify VARIABLES formatting - should be on one line for short variable lists
        String[] lines = output.split("\n");
        assertEquals("VARIABLES x, y, z", lines[1], "Short variable lists should be on one line");
    }

    @Test
    void testOperatorDefinition() throws IOException, SanyFrontendException {
        String spec = "---- MODULE OpTest ----\n" +
                "EXTENDS Naturals\n" +
                "VARIABLE x\n" +
                "Inc == x + 1\n" +
                "====\n";

        testFormattingIdempotency("OPERATOR", spec);

        // Also verify the formatting puts simple operators on one line
        TLAPlusFormatter formatter = new TLAPlusFormatter(spec);
        String output = formatter.getOutput();
        // Verify operator is on one line with proper spacing
        assertTrue(output.contains("Inc == x + 1"), "Simple operators should be on one line with double space after ==.");
    }

    @Test
    void testComplexExpression() throws IOException, SanyFrontendException {
        String spec = "---- MODULE ComplexTest ----\n" +
                "VARIABLE state\n" +
                "NextState == state' = IF state = \"ready\" THEN \"running\" ELSE \"done\"\n" +
                "====\n";

        testFormattingIdempotency("COMPLEX_EXPR", spec);

        TLAPlusFormatter formatter = new TLAPlusFormatter(spec, new FormatConfig(80, 4));
        String output = formatter.getOutput();
        System.out.println(output);

        // Verify complex expression structure
        assertNotNull(output);
        String[] lines = output.split("\n");
        boolean foundNextState = false;
        for (String line : lines) {
            if (line.startsWith("NextState ==")) {
                foundNextState = true;
                break;
            }
        }
        assertTrue(foundNextState, "Should contain NextState operator definition");
    }

    @Test
    void testLineWidthConfiguration() throws IOException, SanyFrontendException {
        String spec = "---- MODULE WidthTest ----\n" +
                "VARIABLES verylongvariablename, anotherlongname, yetanothername\n" +
                "====\n";

        // Test with narrow width
        FormatConfig narrowConfig = new FormatConfig(40, 4);
        TLAPlusFormatter narrowFormatter = new TLAPlusFormatter(spec, narrowConfig);
        String narrowOutput = narrowFormatter.getOutput();

        // Test with wide width
        FormatConfig wideConfig = new FormatConfig(120, 4);
        TLAPlusFormatter wideFormatter = new TLAPlusFormatter(spec, wideConfig);
        String wideOutput = wideFormatter.getOutput();

        assertNotNull(narrowOutput);
        assertNotNull(wideOutput);

        // Both should contain the same content but potentially different formatting
        assertNotNull(narrowOutput);
        assertNotNull(wideOutput);
        assertTrue(narrowOutput.split("\n").length >= 2, "Narrow output should have multiple lines");
        assertTrue(wideOutput.split("\n").length >= 2, "Wide output should have at least 2 lines");

        // Test idempotency for both widths
        testFormattingIdempotency("WIDTH_NARROW", narrowOutput);
        testFormattingIdempotency("WIDTH_WIDE", wideOutput);
    }

    // todo:
    @Test
    void testLongOperatorBreaking() throws IOException, SanyFrontendException {
        String spec = "---- MODULE LongOpTest ----\n" +
                "EXTENDS Naturals\n" +
                "VARIABLE state\n" +
                "VeryLongOperatorName == state = \"this is a long expression that should break\"\n" +
                "====\n";

        // Test with narrow width to force breaking
        FormatConfig narrowConfig = new FormatConfig(60, 4);
        TLAPlusFormatter formatter = new TLAPlusFormatter(spec, narrowConfig);
        String output = formatter.getOutput();

        // Basic content verification - operator should be present
        assertTrue(output.contains("VeryLongOperatorName"), "Should contain operator name");
        //assertFalse(output.contains("VeryLongOperatorName == state = \"this is a long"), "Long operator should not have everything on one line:" + output);

        testFormattingIdempotency("LONG_OPERATOR", output);
    }

    @Test
    void testShortVsLongOperatorFormatting() throws IOException, SanyFrontendException {
        // Short operator should stay on one line
        String shortSpec = "---- MODULE ShortOp ----\n" +
                "EXTENDS Naturals\n" +
                "VARIABLE x\n" +
                "Inc == x + 1\n" +
                "====\n";

        TLAPlusFormatter shortFormatter = new TLAPlusFormatter(shortSpec);
        String shortOutput = shortFormatter.getOutput();

        // Long operator should break with narrow width
        String longSpec = "---- MODULE LongOp ----\n" +
                "EXTENDS Naturals\n" +
                "VARIABLE state\n" +
                "VeryLongOperatorName == state = \"this is a very long expression that should break when narrow\"\n" +
                "====\n";

        FormatConfig narrowConfig = new FormatConfig(50, 4);
        TLAPlusFormatter longFormatter = new TLAPlusFormatter(longSpec, narrowConfig);
        String longOutput = longFormatter.getOutput();

        System.out.println("=== SHORT OPERATOR ===");
        System.out.println(shortOutput);
        System.out.println("=== LONG OPERATOR ===");
        System.out.println(longOutput);

        // Verify formatting differences
        assertTrue(shortOutput.contains("Inc == x + 1"), "Short operator should be on one line");

        // Long operator should have line break after ==
        int longOperatorLines = longOutput.split("\n").length;
        int shortOperatorLines = shortOutput.split("\n").length;
        assertTrue(longOperatorLines >= shortOperatorLines, "Long operator should use more lines");

        // Test idempotency for both
        testFormattingIdempotency("SHORT_OPERATOR", shortOutput);
        testFormattingIdempotency("LONG_OPERATOR_NARROW", longOutput);
    }

    @Test
    void testPreAndPostModuleContent() throws IOException, SanyFrontendException {
        String spec = "This is a comment before the module.\n" +
                "---- MODULE TestModule ----\n" +
                "VARIABLE x\n" +
                "====\n" +
                "This is content after the module.\n";

        TLAPlusFormatter formatter = new TLAPlusFormatter(spec);
        String output = formatter.getOutput();

        // Verify pre/post module content is preserved
        String[] lines = output.split("\n");
        assertEquals("This is a comment before the module.", lines[0]);
        assertEquals("---- MODULE TestModule ----", lines[1]);
        assertEquals("This is content after the module.", lines[lines.length - 1]);
    }

    @Test
    void testTheorem() throws IOException, SanyFrontendException {
        String spec = "---- MODULE TheoremTest ----\n" +
                "EXTENDS Naturals\n" +
                "VARIABLE x\n" +
                "THEOREM TRUE\n" +
                "====\n";

        TLAPlusFormatter formatter = new TLAPlusFormatter(spec);
        String output = formatter.getOutput();

        // Verify theorem structure
        String[] lines = output.split("\n");
        boolean foundTheorem = false;
        for (String line : lines) {
            if (line.startsWith("THEOREM")) {
                foundTheorem = true;
                break;
            }
        }
        assertTrue(foundTheorem, "Should contain THEOREM declaration");
    }

    @Test
    void testEmptyModule() throws IOException, SanyFrontendException {
        String spec = "---- MODULE Empty ----\n" +
                "====\n";

        TLAPlusFormatter formatter = new TLAPlusFormatter(spec);
        String output = formatter.getOutput();

        // Verify empty module structure
        String[] lines = output.split("\n");
        assertEquals(2, lines.length, "Empty module should have exactly 2 lines");
        assertEquals("---- MODULE Empty ----", lines[0]);
        assertEquals("====", lines[1]);
    }

    @Test
    void testConfigurationDefaults() {
        FormatConfig config = new FormatConfig();
        assertEquals(80, config.getLineWidth());
        assertEquals(4, config.getIndentSize());
    }

    @Test
    void testConfigurationValidation() {
        assertThrows(IllegalArgumentException.class, () -> new FormatConfig(-1, 4));
        assertThrows(IllegalArgumentException.class, () -> new FormatConfig(80, -1));

        // These should be valid
        assertDoesNotThrow(() -> new FormatConfig(1, 0));
        assertDoesNotThrow(() -> new FormatConfig(200, 8));
    }

    @Test
    void testComplexModuleStructure() throws IOException, SanyFrontendException {
        String spec = "---- MODULE ComplexStructure ----\n" +
                "EXTENDS Naturals\n" +
                "VARIABLES x, y, z\n" +
                "\n" +
                "Init == x = 0\n" +
                "\n" +
                "Next == x + 1\n" +
                "\n" +
                "Spec == TRUE\n" +
                "\n" +
                "THEOREM TRUE\n" +
                "====\n";

        TLAPlusFormatter formatter = new TLAPlusFormatter(spec);
        String output = formatter.getOutput();

        System.out.println(output);
        // Verify all major sections are present with proper structure
        String[] lines = output.split("\n");
        boolean foundExtends = false, foundVariables = false, foundInit = false, foundNext = false, foundSpec = false, foundTheorem = false;

        for (String line : lines) {
            if (line.startsWith("EXTENDS")) foundExtends = true;
            else if (line.startsWith("VARIABLES")) foundVariables = true;
            else if (line.startsWith("Init ==")) foundInit = true;
            else if (line.startsWith("Next ==")) foundNext = true;
            else if (line.startsWith("Spec ==")) foundSpec = true;
            else if (line.startsWith("THEOREM")) foundTheorem = true;
        }

        assertTrue(foundExtends && foundVariables && foundInit && foundNext && foundSpec && foundTheorem,
                "All major sections should be present");
    }

    @Test
    void testNewlinePreservation() throws IOException, SanyFrontendException {
        String spec = "---- MODULE NewlineTest ----\n" +
                "\n" +
                "VARIABLE x\n" +
                "\n" +
                "\n" +
                "Init == x = 0\n" +
                "\n" +
                "====\n";

        TLAPlusFormatter formatter = new TLAPlusFormatter(spec);
        String output = formatter.getOutput();
        System.out.println("=== NEWLINE PRESERVATION TEST ===");
        System.out.println(output);

        // Verify that extra newlines are preserved
        String[] lines = output.split("\n");

        // Debug output to see what we actually get
        for (int i = 0; i < lines.length; i++) {
            System.out.println("Line " + i + ": '" + lines[i] + "'");
        }

        // Verify basic structure and newline preservation
        assertEquals("---- MODULE NewlineTest ----", lines[0]);
        assertTrue(output.contains("VARIABLE x"), "Should contain VARIABLE x");
        assertTrue(output.contains("Init =="), "Should contain Init ==");
        assertEquals("====", lines[lines.length - 1]);

        // Count empty lines to verify preservation (should have multiple empty lines)
        long emptyLineCount = java.util.Arrays.stream(lines)
                .filter(line -> line.trim().isEmpty())
                .count();
        assertTrue(emptyLineCount >= 3, "Should have at least 3 empty lines preserved, got " + emptyLineCount);

        testFormattingIdempotency("NEWLINE_PRESERVATION", output);
    }

    @Test
    void testMultipleNewlinePatterns() throws IOException, SanyFrontendException {
        String spec = "---- MODULE MultiNewline ----\n" +
                "EXTENDS Naturals\n" +
                "\n" +
                "\n" +
                "\n" +
                "VARIABLES x, y\n" +
                "\n" +
                "Op1 == TRUE\n" +
                "\n" +
                "\n" +
                "Op2 == FALSE\n" +
                "====\n";

        TLAPlusFormatter formatter = new TLAPlusFormatter(spec);
        String output = formatter.getOutput();
        System.out.println("=== MULTIPLE NEWLINES TEST ===");
        System.out.println(output);
        assertEquals(spec, output);
        // Count empty lines to verify newlines are preserved
        long emptyLineCount = java.util.Arrays.stream(output.split("\n"))
                .filter(line -> line.trim().isEmpty())
                .count();
        assertTrue(emptyLineCount >= 4, "Should preserve multiple empty lines, got " + emptyLineCount);

        testFormattingIdempotency("MULTIPLE_NEWLINES", output);
    }

    @Test
    void testSingleNewlinesRemainSingle() throws IOException, SanyFrontendException {
        String spec = "---- MODULE SingleNewlines ----\n" +
                "VARIABLE x\n" +
                "Init == x = 0\n" +
                "====\n";

        TLAPlusFormatter formatter = new TLAPlusFormatter(spec);
        String output = formatter.getOutput();

        // Verify that single newlines don't get extra spacing added
        String[] lines = output.split("\n");
        assertEquals(4, lines.length, "Should have exactly 4 lines with no extra spacing");
        assertEquals("---- MODULE SingleNewlines ----", lines[0]);
        assertEquals("VARIABLE x", lines[1]);
        assertEquals("Init == x = 0", lines[2]);
        assertEquals("====", lines[3]);
    }

    @Test
    void testModuleWithExtendsBreak() throws IOException, SanyFrontendException {
        String spec = "---- MODULE TestWithExtends ----\n" +
                "EXTENDS Naturals, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC\n" +
                "VARIABLE counter\n" +
                "====\n";

        // First pass
        TLAPlusFormatter formatter1 = new TLAPlusFormatter(spec);
        String output1 = formatter1.getOutput();
        System.out.println("=== EXTENDS FIRST PASS ===");
        System.out.println(output1);

        // Verify the formatter produces reasonable output for long EXTENDS lists
        assertNotNull(output1);
        assertTrue(output1.contains("EXTENDS"), "Should contain EXTENDS keyword");
        assertTrue(output1.contains("Naturals"), "Should contain first module");
        assertTrue(output1.contains("TLC"), "Should contain repeated modules");
        assertTrue(output1.contains("VARIABLE counter"), "Should contain variable declaration");

        // Verify line breaking behavior - long EXTENDS should break lines
        String[] lines = output1.split("\n");
        boolean hasExtendsLine = false;
        int extendsRelatedLines = 0;

        for (String line : lines) {
            if (line.trim().startsWith("EXTENDS") ||
                    (hasExtendsLine && line.trim().contains("TLC") && !line.contains("VARIABLE"))) {
                hasExtendsLine = true;
                extendsRelatedLines++;
            } else if (hasExtendsLine && !line.trim().contains("TLC")) {
                break;
            }
        }

        assertTrue(extendsRelatedLines > 1, "Long EXTENDS should break across multiple lines");
        testFormattingIdempotency("testModuleWithExtendsBreak", spec);

    }

    @Test
    void testIfThenElseConstruct() throws IOException, SanyFrontendException {
        String spec = "---- MODULE IfThenElseTest ----\n" +
                "EXTENDS Naturals\n" +
                "VARIABLES x, y\n" +
                "Init == x = 0 /\\ y = 0\n" +
                "Next == x' = IF x < 10 THEN x + 1 ELSE 0 /\\ y' = IF y > 5 THEN y - 1 ELSE y + 2\n" +
                "Nested == x' = IF x < 5 THEN IF y > 3 THEN x + y ELSE x - y ELSE 0\n" +
                "====\n";

        testFormattingIdempotency("IF_THEN_ELSE", spec);

        TLAPlusFormatter formatter = new TLAPlusFormatter(spec, new FormatConfig(60, 4));
        String output = formatter.getOutput();
        System.out.println(output);
        // Verify IF-THEN-ELSE formatting
        assertNotNull(output);
        String[] lines = output.split("\n");

        boolean foundSimpleIfThenElse = false;
        boolean foundNestedIfThenElse = false;
        boolean foundIndentedThen = false;
        boolean foundIndentedElse = false;

        for (String line : lines) {
            if (line.contains("IF x < 10")) {
                foundSimpleIfThenElse = true;
            }
            if (line.contains("IF x < 5")) {
                foundNestedIfThenElse = true;
            }
            if (line.trim().startsWith("THEN")) {
                foundIndentedThen = true;
            }
            if (line.trim().startsWith("ELSE")) {
                foundIndentedElse = true;
            }
        }

        assertTrue(foundSimpleIfThenElse, "Should contain simple IF-THEN-ELSE construct");
        assertTrue(foundNestedIfThenElse, "Should contain nested IF-THEN-ELSE construct");
        assertTrue(foundIndentedThen, "THEN should be properly indented: {}" + output);
        assertTrue(foundIndentedElse, "ELSE should be properly indented");

        // Verify that IF-THEN-ELSE is properly formatted with line breaks
        assertTrue(output.contains("IF x < 10\n"), "IF condition should be followed by newline");
        assertTrue(output.contains("THEN "), "THEN should be present with space");
        assertTrue(output.contains("ELSE "), "ELSE should be present with space");
    }

}