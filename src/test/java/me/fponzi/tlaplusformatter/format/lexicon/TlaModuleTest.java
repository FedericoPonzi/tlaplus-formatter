package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.LexiconTest;
import org.junit.jupiter.api.Test;

class TlaModuleTest extends LexiconTest {
    @Test
    void testFormatModule() {
        var spec = "---- MODULE Spec ----\n======\n";
        var expected = "---- MODULE Spec ----\n======\n";
        assertSpecEquals(expected, spec);
    }

    @Test
    void testFormatModule2() {
        var spec = "---- MODULE Spec ----\n\n======";
        var expected = "---- MODULE Spec ----\n\n======";
        assertSpecEquals(expected, spec);
    }

}