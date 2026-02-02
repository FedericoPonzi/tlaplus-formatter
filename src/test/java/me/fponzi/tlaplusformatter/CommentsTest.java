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


}
