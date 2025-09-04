package me.fponzi.tlaplusformatter;

import me.fponzi.tlaplusformatter.exceptions.SanyFrontendException;
import me.fponzi.tlasmith.TLASmith;
import net.jqwik.api.*;
import org.junit.jupiter.api.Disabled;
import tla2sany.st.TreeNode;

import java.io.IOException;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class PropertyBasedFormatterTest extends LexiconTest {
    // this is just for debugging purposes
    // it will print out some of the generated specs and their formatted versions
    @Property(tries = 3)
    @Disabled
    void showExampleSpecs(@ForAll("validTlaSpecs")
                          String spec)
            throws IOException,
            SanyFrontendException {
        System.err.println("=== Generated TLA+ Spec ===");
        System.err.println(spec);
        System.err.println("=== After Formatting ===");
        try {
            System.err.println(format(spec));
        } catch (Exception e) {
            System.err.println("FORMATTING ERROR: " + e.getMessage());
            System.err.println("Failed spec: " + spec);
        }
        System.err.println("*******************");
    }

    @Property
    void formatterPreservesSemantics(@ForAll("validTlaSpecs") String spec)
            throws IOException, SanyFrontendException {
        try {
            String formatted = format(spec);
            TreeNode originalAst = parse(spec);
            TreeNode formattedAst = parse(formatted);

            assertTrue(compareAst(originalAst, formattedAst),
                    "AST should be preserved after formatting");
        } catch (Exception e) {
            System.err.println("Failed spec: " + spec);
            throw e;
        }
    }

    @Property
    void formatterIsIdempotent(@ForAll("validTlaSpecs") String spec)
            throws IOException, SanyFrontendException {
        String formatted = format(spec);
        String doubleFormatted = format(formatted);

        assertEquals(formatted, doubleFormatted,
                "Formatter should be idempotent");
    }

    private String format(String spec) throws IOException, SanyFrontendException {
        return new TLAPlusFormatter(spec).getOutput();
    }

    private TreeNode parse(String spec) throws IOException, SanyFrontendException {
        return new TLAPlusFormatter(spec).root;
    }

    @Provide
    Arbitrary<String> validTlaSpecs() {
        return Arbitraries.integers().between(1, 10000).map(seed -> {
            try {
                return TLASmith.toTLAString(TLASmith.generateSpec("PropTest", seed));
            } catch (Exception e) {
                System.err.println("Failed to generate spec with seed: " + seed);
                throw e;
            }
        });
    }


}