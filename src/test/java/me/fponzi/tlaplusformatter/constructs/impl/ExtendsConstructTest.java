package me.fponzi.tlaplusformatter.constructs.impl;

import org.junit.jupiter.api.Test;

import static me.fponzi.tlaplusformatter.Utils.assertUnchanged;

class ExtendsConstructTest {

    @Test
    void testExtendsWithCommentsOnMultipleModules() {
        // Comments after non-last EXTENDS modules are preserved as pre-comments
        // on the following module node. The comment after the last module goes to the
        // next construct keyword (VARIABLE), which is handled by that construct.
        String spec = "---- MODULE TestExtendsComments ----\n" +
                "EXTENDS Naturals,\n" +
                "        TLC,\n" +
                "        Sequences, \\* Trace operator\n" +
                "        FiniteSets\n" +
                "VARIABLE x\n" +
                "====\n";
        assertUnchanged(spec);
    }

    @Test
    void testExtendsWithCommentOnEveryNonLastModule() {
        String spec = "---- MODULE TestExtendsAllComments ----\n" +
                "EXTENDS Naturals, \\* basic math\n" +
                "        Sequences, \\* sequence ops\n" +
                "        FiniteSets\n" +
                "VARIABLE x\n" +
                "====\n";
        assertUnchanged(spec);
    }

    @Test
    void testExtendsWithCommentsOnAllNonLastModulesFour() {
        String spec = "---- MODULE TestExtendsFourComments ----\n" +
                "EXTENDS Naturals, \\* basic math\n" +
                "        Sequences, \\* sequence ops\n" +
                "        FiniteSets, \\* finite set ops\n" +
                "        TLC\n" +
                "VARIABLE x\n" +
                "====\n";
        assertUnchanged(spec);
    }

    @Test
    void testExtendsWithBlockCommentOnModule() {
        String spec = "---- MODULE TestExtendsBlockComment ----\n" +
                "EXTENDS Naturals,\n" +
                "        (* utility module *)\n" +
                "        TLC\n" +
                "VARIABLE x\n" +
                "====\n";
        assertUnchanged(spec);
    }
}
