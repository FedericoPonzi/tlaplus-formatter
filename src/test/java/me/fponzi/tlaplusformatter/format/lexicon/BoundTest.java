package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.LexiconTest;
import org.junit.jupiter.api.Test;

public class BoundTest extends LexiconTest  {
    @Test
    public void testBound() {
        var spec = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals, Sequences\n" +
                "CONSTANT a\n" +
                "Support(x) == 0\n" +
                "R ** T == LET SR == Support(R)\n" +
                "              ST == Support(T)\n" +
                "          IN  {<<r, t>> \\in SR \\X ST :\n" +
                "                \\E s \\in SR \\cap ST : (<<r, s>> \\in R) /\\ (<<s, t>> \\in T)}\n" +
                "====\n";
        var expected = "----- MODULE Spec -----\n" +
                "EXTENDS Naturals, Sequences\n" +
                "CONSTANT\n" +
                "         a\n" +
                "Support(x) ==\n" +
                "              0\n" +
                "R ** T ==\n" +
                "          LET\n" +
                "              SR ==\n" +
                "                    Support(R)\n" +
                "              ST ==\n" +
                "                    Support(T)\n" +
                "          IN\n" +
                "              { <<r,t>> \\in SR \\X ST: \\E s \\in SR \\cap ST: (<<r, s>> \\in R) /\\ (<<s, t>> \\in T) }\n" +
                "====\n";
        assertSpecEquals(expected, spec);
    }
}
