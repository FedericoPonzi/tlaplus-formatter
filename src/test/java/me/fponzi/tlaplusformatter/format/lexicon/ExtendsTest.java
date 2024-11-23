package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.LexiconTest;
import org.junit.jupiter.api.Test;

public class ExtendsTest extends LexiconTest {
    @Test
    void testFormatExtends() {
        var spec = "---- MODULE Spec ----\nEXTENDS Naturals\n======";
        var expected = "---- MODULE Spec ----\nEXTENDS Naturals\n======";
        assertSpecEquals(expected, spec);
    }
}
