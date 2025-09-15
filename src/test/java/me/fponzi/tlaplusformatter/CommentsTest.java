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
