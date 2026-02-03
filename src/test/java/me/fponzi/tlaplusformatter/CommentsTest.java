package me.fponzi.tlaplusformatter;

import org.junit.jupiter.api.Test;

import static me.fponzi.tlaplusformatter.Utils.assertSpecEquals;


public class CommentsTest {
    @Test
    public void moduleLevelCommentBlock() {
        var input = "---------- MODULE TowerOfHanoi -----\n" +
                "EXTENDS Naturals\n" +
                "\n" +
                "(***************************************************************************)\n" +
                "(* TRUE iff i is a power of two                                            *)\n" +
                "(***************************************************************************)\n" +
                "IsTwo(i) == i - 2 = 0\n" +
                "====";
        var expected = "---------- MODULE TowerOfHanoi -----\n" +
                "EXTENDS Naturals\n" +
                "\n" +
                "(***************************************************************************)\n" +
                "(* TRUE iff i is a power of two                                            *)\n" +
                "(***************************************************************************)\n" +
                "IsTwo(i) == i - 2 = 0\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void moduleLevelCommentInline() {
        var input = "---------- MODULE TowerOfHanoi -----\n" +
                "EXTENDS Naturals\n" +
                "\n" +
                "\\* TRUE iff i is a power of two\n" +
                "IsTwo(i) == i - 2 = 0\n" +
                "====";
        var expected = "---------- MODULE TowerOfHanoi -----\n" +
                "EXTENDS Naturals\n" +
                "\n" +
                "\\* TRUE iff i is a power of two\n" +
                "IsTwo(i) == i - 2 = 0\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void variablesWithInlineComments() {
        // This tests that inline comments on multi-line VARIABLES declarations are preserved.
        // In SANY's AST, inline comments after a token are stored as pre-comments of the NEXT token.
        // So "clock, \* local clock" has the comment stored as pre-comment of "req".
        // The trailing comment after the last variable is attached to the next declaration.
        var input = "---------- MODULE Test -----\n" +
                "VARIABLES\n" +
                "  clock,    \\* local clock\n" +
                "  req       \\* requests\n" +
                "\n" +
                "Init == TRUE\n" +
                "====";
        // The formatted output preserves comments, but trailing comment moves to next line
        var expected = "---------- MODULE Test -----\n" +
                "VARIABLES\n" +
                "  clock,    \\* local clock\n" +
                "  req\n" +
                "\\* requests\n" +
                "Init == TRUE\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void variablesWithMultiLineBlockComments() {
        // This tests that multi-line block comments following VARIABLES declarations
        // are preserved correctly, not joined on a single line with commas between them.
        // This is a bug that was causing parse errors in specifications/Prisoners/Prisoners.tla
        var input = "---------- MODULE Test -----\n" +
                "VARIABLES\n" +
                "  switchAUp,\n" +
                "  switchBUp,\n" +
                "    (***********************************************************************)\n" +
                "    (* The states of the two switches, represented by boolean-valued       *)\n" +
                "    (* variables.                                                          *)\n" +
                "    (***********************************************************************)\n" +
                "  count\n" +
                "\n" +
                "Init == TRUE\n" +
                "====";
        // Block comments should be on separate lines, not joined with commas
        var expected = "---------- MODULE Test -----\n" +
                "VARIABLES\n" +
                "  switchAUp,\n" +
                "  switchBUp,\n" +
                "    (***********************************************************************)\n" +
                "    (* The states of the two switches, represented by boolean-valued       *)\n" +
                "    (* variables.                                                          *)\n" +
                "    (***********************************************************************)\n" +
                "  count\n" +
                "\n" +
                "Init == TRUE\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void commentsPreserveTrailingWhitespace() {
        // Trailing whitespace in comments should be preserved because SANY's AST
        // preserves it, and stripping it changes semantic equality.
        var input = "---------- MODULE Test -----\n" +
                "EXTENDS Naturals\n" +
                "\n" +
                "\\* Comment with trailing space \n" +
                "IsTwo(i) == i - 2 = 0\n" +
                "====";
        var expected = "---------- MODULE Test -----\n" +
                "EXTENDS Naturals\n" +
                "\n" +
                "\\* Comment with trailing space \n" +
                "IsTwo(i) == i - 2 = 0\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void constantsWithInlineComments() {
        // This tests that inline comments on multi-line CONSTANT declarations are preserved.
        // Similar to VARIABLES, SANY stores inline comments as pre-comments of the NEXT token.
        var input = "---------- MODULE Test -----\n" +
                "CONSTANT Jug,      \\* The set of all jugs.\n" +
                "         Capacity, \\* Capacity of each jug.\n" +
                "         Goal      \\* The goal amount.\n" +
                "\n" +
                "Init == TRUE\n" +
                "====";
        // The formatted output preserves comments. The trailing comment moves to the next line.
        var expected = "---------- MODULE Test -----\n" +
                "CONSTANT Jug,    \\* The set of all jugs.\n" +
                "         Capacity,    \\* Capacity of each jug.\n" +
                "         Goal\n" +
                "\\* The goal amount.\n" +
                "Init == TRUE\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void constantsWithOperatorParameters() {
        // This tests that CONSTANT declarations with operator parameters like Op(_,_)
        // preserve their parameters when formatted with comments.
        var input = "---------- MODULE Test -----\n" +
                "CONSTANTS\n" +
                "    Hash,                   \\* Comment 1\n" +
                "    CalculateHash(_,_,_),   \\* Comment 2\n" +
                "    Other                   \\* Comment 3\n" +
                "\n" +
                "ASSUME TRUE\n" +
                "====";
        // The operator parameters should be preserved
        var expected = "---------- MODULE Test -----\n" +
                "CONSTANTS Hash,    \\* Comment 1\n" +
                "         CalculateHash(_,_,_),    \\* Comment 2\n" +
                "         Other\n" +
                "\\* Comment 3\n" +
                "ASSUME TRUE\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void localInstanceWithBlockComment() {
        // This tests that block comments before LOCAL INSTANCE declarations are preserved.
        var input = "---------- MODULE Test -----\n" +
                "(* Block comment *)\n" +
                "LOCAL INSTANCE Naturals\n" +
                "====";
        var expected = "---------- MODULE Test -----\n" +
                "(* Block comment *)\n" +
                "LOCAL INSTANCE Naturals\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void commentsRespectProperIndentationContext() {
        var input = "---------- MODULE TestModule -----\n" +
                "EXTENDS Naturals\n" +
                "\n" +
                "Foo == \n" +
                "  LET \n" +
                "    (* This comment should be indented to match the LET context *)\n" +
                "    (* Even if the original has extra indentation *)\n" +
                "    x == 1\n" +
                "  IN x + 1\n" +
                "====";
        var expected = "---------- MODULE TestModule -----\n" +
                "EXTENDS Naturals\n" +
                "\n" +
                "Foo == LET (* This comment should be indented to match the LET context *)\n" +
                "           (* Even if the original has extra indentation *)\n" +
                "           x == 1 IN x + 1\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void variablesWithCommentBeforeFirstVariable() {
        // This tests that a comment BEFORE the first variable is preserved.
        // The comment appears as preComment on the first variable node.
        var input = "---------- MODULE Test -----\n" +
                "VARIABLES\n" +
                "    \\* type annotation\n" +
                "    x\n" +
                "\n" +
                "Init == TRUE\n" +
                "====";
        var expected = "---------- MODULE Test -----\n" +
                "VARIABLES\n" +
                "    \\* type annotation\n" +
                "  x\n" +
                "\n" +
                "Init == TRUE\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void tupleWithPrecedingComments() {
        // This tests that line comments before a tuple expression are preserved.
        // The comments are attached to the opening << bracket in SANY's AST.
        var input = "---------- MODULE Test -----\n" +
                "Foo ==\n" +
                "\\* Comment before tuple\n" +
                "<<1, 2>>\n" +
                "====";
        // Comment is preserved but formatting puts it inline after ==
        var expected = "---------- MODULE Test -----\n" +
                "Foo == \\* Comment before tuple\n" +
                "  << 1, 2 >>\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void constantsWithCommentBeforeFirstConstant() {
        // This tests that a comment BEFORE the first constant is preserved.
        // The comment appears as preComment on the constant node.
        var input = "---------- MODULE Test -----\n" +
                "CONSTANTS\n" +
                "    \\* Number of philosophers\n" +
                "    NP\n" +
                "\n" +
                "ASSUME TRUE\n" +
                "====";
        var expected = "---------- MODULE Test -----\n" +
                "CONSTANTS\n" +
                "    \\* Number of philosophers\n" +
                "    NP\n" +
                "\n" +
                "ASSUME TRUE\n" +
                "====";
        assertSpecEquals(expected, input);
    }

}
