package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.SanyTester;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class TlaModuleTest extends SanyTester {
    @Test
    void testFormatModule() {
        var spec = "---- MODULE Spec ----\n======";
        var expected = "---- MODULE Spec ----\n\n======\n";
        assertSpecEquals(expected, spec);
    }

    @Test
    void testFormatModule2() {
        var spec = "---- MODULE Spec ----\n\n======";
        var expected = "---- MODULE Spec ----\n\n======\n";
        assertSpecEquals(expected, spec);
    }

}