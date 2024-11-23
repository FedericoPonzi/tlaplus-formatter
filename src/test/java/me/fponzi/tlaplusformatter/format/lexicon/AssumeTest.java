package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.LexiconTest;
import org.junit.jupiter.api.Test;

public class AssumeTest extends LexiconTest {
    @Test
    public void testFormatAssume() {
        var spec = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals\n" +
                "CONSTANT x\n" +
                "ASSUME x \\in Nat\n" +
                "====\n";

        var expected = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals\n" +
                "CONSTANT\n" +
                "         x\n" +
                "ASSUME\n" +
                "       x \\in Nat\n" +
                "====\n";
        assertSpecEquals(expected, spec);
    }

    @Test
    public void testFormatAssumeConjList() {
        var spec = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals\n" +
                "CONSTANT x\n" +
                "ASSUME /\\ x \\in Nat\n" +
                "       /\\ x > 10\n" +
                "====\n";

        var expected = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals\n" +
                "CONSTANT\n" +
                "         x\n" +
                "ASSUME\n" +
                "       /\\ x \\in Nat\n" +
                "       /\\ x > 10\n" +
                "====\n";
        assertSpecEquals(expected, spec);
    }

}
