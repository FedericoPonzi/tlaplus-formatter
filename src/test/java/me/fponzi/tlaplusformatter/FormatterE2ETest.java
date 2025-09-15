package me.fponzi.tlaplusformatter;

import me.fponzi.tlaplusformatter.exceptions.SanyFrontendException;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static me.fponzi.tlaplusformatter.Utils.assertSpecEquals;
import static me.fponzi.tlaplusformatter.Utils.assertSpecUnchanged;
import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * End-to-end tests for the TLA+ formatter.
 * These tests create TLA+ specifications as strings, format them,
 * and verify the output structure and formatting quality.
 */
class FormatterE2ETest {

    @Test
    void testSimpleModuleFormatting() {
        String spec = "---- MODULE SimpleTest ----\n" +
                "VARIABLE x\n" +
                "Init == x = 0\n" +
                "====\n";
        assertSpecUnchanged(spec);
    }

    @Test
    void testModuleWithExtends() {
        String spec = "---- MODULE TestWithExtends ----\n" +
                "EXTENDS Naturals, TLC\n" +
                "VARIABLE counter\n" +
                "====\n";
        assertSpecUnchanged(spec);
    }

    @Test
    void testMultipleVariables() {
        String spec = "---- MODULE MultiVar ----\n" +
                "VARIABLES x, y, z\n" +
                "====\n";
        assertSpecUnchanged(spec);
    }

    @Test
    void testOperatorDefinition() {
        String spec = "---- MODULE OpTest ----\n" +
                "EXTENDS Naturals\n" +
                "VARIABLE x\n" +
                "Inc == x + 1\n" +
                "====\n";

        assertSpecUnchanged(spec);
    }

    @Test
    void testComplexExpression() throws IOException, SanyFrontendException {
        String spec = "---- MODULE ComplexTest ----\n" +
                "VARIABLE state\n" +
                "NextState == state' = IF state = \"ready\" THEN \"running\" ELSE \"done\"\n" +
                "====\n";
        assertSpecUnchanged(spec);
    }

    @Test
    void testLineWidthConfiguration() throws IOException, SanyFrontendException {
        String spec = "---- MODULE WidthTest ----\n" +
                "VARIABLES verylongvariablename, anotherlongname, yetanothername, abc\n" +
                "====\n";
        assertSpecUnchanged(spec);
        String wrapped = "---- MODULE WidthTest ----\n" +
                "VARIABLES verylongvariablename,\n" +
                "          anotherlongname,\n" +
                "          yetanothername,\n" +
                "          abc\n" +
                "====\n";
        assertSpecEquals(wrapped, spec, 20);
    }

    @Test
    void testLongOperatorBreaking() {
        String spec = "---- MODULE LongOpTest ----\n" +
                "EXTENDS Naturals\n" +
                "VARIABLE state\n" +
                "VeryLongOperatorName == state = \"this is a long expression that should break\"\n" +
                "====\n";
        String wrapped = "---- MODULE LongOpTest ----\n" +
                "EXTENDS Naturals\n" +
                "VARIABLE state\n" +
                "VeryLongOperatorName ==\n" +
                "  state = \"this is a long expression that should break\"\n" +
                "====\n";
        assertSpecUnchanged(spec);
        assertSpecEquals(wrapped, spec, 60);
    }

    @Test
    void testShortVsLongOperatorFormatting() throws IOException, SanyFrontendException {
        // Short operator should stay on one line
        String shortSpec = "---- MODULE ShortOp ----\n" +
                "EXTENDS Naturals\n" +
                "VARIABLE x\n" +
                "Inc == x + 1\n" +
                "====\n";
        assertSpecUnchanged(shortSpec);

        // Long operator should break with narrow width
        String longSpec = "---- MODULE LongOp ----\n" +
                "EXTENDS Naturals\n" +
                "VARIABLE state\n" +
                "VeryLongOperatorName == state = \"this is a very long expression that should break when narrow\"\n" +
                "====\n";
        String expectedWrapped = "---- MODULE LongOp ----\n" +
                "EXTENDS Naturals\n" +
                "VARIABLE state\n" +
                "VeryLongOperatorName ==\n" +
                "  state =\n" +
                "    \"this is a very long expression that should break when narrow\"\n" +
                "====\n";
        assertSpecEquals(expectedWrapped, longSpec, 40);
    }

    @Test
    void testPreAndPostModuleContent() throws IOException, SanyFrontendException {
        String spec = "This is a comment before the module.\n" +
                "---- MODULE TestModule ----\n" +
                "VARIABLE x\n" +
                "====\n" +
                "This is content after the module.\n";
        assertSpecUnchanged(spec);
    }

    @Test
    void testTheorem() throws IOException, SanyFrontendException {
        String spec = "---- MODULE TheoremTest ----\n" +
                "EXTENDS Naturals\n" +
                "VARIABLE x\n" +
                "THEOREM TRUE\n" +
                "====\n";
        assertSpecUnchanged(spec);
    }

    @Test
    void testEmptyModule() throws IOException, SanyFrontendException {
        String spec = "---- MODULE Empty ----\n" +
                "====\n";
        assertSpecUnchanged(spec);
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
        assertSpecUnchanged(spec);
    }

    @Test
    void testNewlinePreservation() throws IOException, SanyFrontendException {
        String spec = "---- MODULE NewlineTest ----\n" +
                //"\n" + TODO: currently removing leading newlines
                "VARIABLE x\n" +
                "\n" +
                "\n" +
                "Init == x = 0\n" +
                "\n" +
                "====\n";
        assertSpecUnchanged(spec);
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
        assertSpecUnchanged(spec);
    }

    @Test
    void testSingleNewlinesRemainSingle() throws IOException, SanyFrontendException {
        String spec = "---- MODULE SingleNewlines ----\n" +
                "VARIABLE x\n" +
                "Init == x = 0\n" +
                "====\n";
        assertSpecUnchanged(spec);
    }

    @Test
    void testModuleWithExtendsBreak() throws IOException, SanyFrontendException {
        String spec = "---- MODULE TestWithExtends ----\n" +
                "EXTENDS Naturals, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC, TLC\n" +
                "VARIABLE counter\n" +
                "====\n";
        String wrapped = "---- MODULE TestWithExtends ----\n" +
                "EXTENDS Naturals,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC\n" +
                "VARIABLE counter\n" +
                "====\n";
        assertSpecEquals(wrapped, spec);

    }
}