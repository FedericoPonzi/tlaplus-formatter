package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.LexiconTest;
import org.junit.jupiter.api.Test;

public class ParamDeclarationTest extends LexiconTest {
    @Test
    public void testConstants() {
        // using Constants
        var spec = "----- MODULE Spec -----\n" +
                "\n" +
                "CONSTANTS x, y\n" +
                "====\n";
        var expected = "----- MODULE Spec -----\n" +
                "\n" +
                "CONSTANTS\n" +
                "          x,\n" +
                "          y\n" +
                "====\n";
        assertSpecEquals(expected, spec);
    }

    @Test
    public void testConstantsParamsIdentDecl() {
        // using Constants
        var spec = "----- MODULE Spec -----\n" +
                "\n" +
                "CONSTANTS  CalculateHash(_,_,_)\n" +
                "====\n";
        var expected = "----- MODULE Spec -----\n" +
                "\n" +
                "CONSTANTS\n" +
                "          CalculateHash(_,_,_)\n" +
                "====\n";
        assertSpecEquals(expected, spec);

    }

}
