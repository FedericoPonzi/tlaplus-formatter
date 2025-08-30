package me.fponzi.tlaplusformatter;

import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import static me.fponzi.tlaplusformatter.Utils.assertSpecEquals;


public class CommentsTest {
    @Test
    @Disabled
    public void moduleLevelComment() {
        var input = "---------- MODULE TowerOfHanoi -----\n" +
                "EXTENDS Naturals\n" +
                "\n" +
                "(***************************************************************************)\n" +
                "  (* TRUE iff i is a power of two                                            *)\n" +
                "  (***************************************************************************)\n" +
                "  IsTwo(i) == i - 2 = 0\n" +
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

    /*
     * TODO: the precomment is just thrown away by SANY. it will need to be fixed on SANY side
     *  before this can be fixed here.
     */
    @Test
    @Disabled
    public void commentsRespectProperIndentationContext() {
        var input = "---------- MODULE TestModule -----\n" +
                "EXTENDS Naturals\n" +
                "\n" +
                "Foo == \n" +
                "  LET \n" +
                // "    (* This comment should be indented to match the LET context *)\n" +
                //"      (* Even if the original has extra indentation *)\n" +
                "    x == 1\n" +
                "  IN x + 1\n" +
                "====";
        var expected = "---------- MODULE TestModule -----\n" +
                "EXTENDS Naturals\n" +
                "\n" +
                "Foo ==\n" +
                "  LET\n" +
                "    (* This comment should be indented to match the LET context *)\n" +
                "    (* Even if the original has extra indentation *)\n" +
                "    x == 1\n" +
                "  IN x + 1\n" +
                "====";
        assertSpecEquals(expected, input);
    }
}
