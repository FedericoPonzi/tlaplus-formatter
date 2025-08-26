package me.fponzi.tlaplusformatter;

import me.fponzi.tlaplusformatter.exceptions.SanyFrontendException;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests to verify that the formatter is idempotent - 
 * running it multiple times should produce the same output.
 */
class IdempotencyTest {

    @Test
    void testSimpleModuleIdempotency() throws IOException, SanyFrontendException {
        String spec = "---- MODULE SimpleTest ----\n" +
                     "VARIABLE x\n" +
                     "Init == x = 0\n" +
                     "====\n";

        // First formatting pass
        TLAPlusFormatter formatter1 = new TLAPlusFormatter(spec);
        String output1 = formatter1.getOutput();
        
        System.out.println("=== FIRST PASS ===");
        System.out.println(output1);
        
        // Second formatting pass on the output of the first
        TLAPlusFormatter formatter2 = new TLAPlusFormatter(output1);
        String output2 = formatter2.getOutput();
        
        System.out.println("=== SECOND PASS ===");
        System.out.println(output2);
        
        // The outputs should be identical
        assertEquals(output1, output2, "Formatter should be idempotent - second pass should produce same result");
    }

    @Test
    void testComplexModuleIdempotency() throws IOException, SanyFrontendException {
        String spec = "---- MODULE ComplexTest ----\n" +
                     "EXTENDS Naturals\n" +
                     "VARIABLES x, y, z\n" +
                     "Init == x = 0\n" +
                     "Next == x + 1\n" +
                     "====\n";

        // First pass
        TLAPlusFormatter formatter1 = new TLAPlusFormatter(spec);
        String output1 = formatter1.getOutput();
        
        System.out.println("=== COMPLEX FIRST PASS ===");
        System.out.println(output1);
        
        // Second pass
        TLAPlusFormatter formatter2 = new TLAPlusFormatter(output1);
        String output2 = formatter2.getOutput();
        
        System.out.println("=== COMPLEX SECOND PASS ===");
        System.out.println(output2);
        
        assertEquals(output1, output2, "Complex formatter should be idempotent");
    }

    @Test
    void testMultipleRoundsStability() throws IOException, SanyFrontendException {
        String spec = "---- MODULE StabilityTest ----\n" +
                     "EXTENDS Naturals, TLC\n" +
                     "VARIABLES a, b, c\n" +
                     "Op1 == a + b\n" +
                     "Op2 == TRUE\n" +
                     "====\n";

        String current = spec;
        
        // Run formatter 5 times
        for (int i = 1; i <= 5; i++) {
            TLAPlusFormatter formatter = new TLAPlusFormatter(current);
            String next = formatter.getOutput();
            
            System.out.println("=== ROUND " + i + " ===");
            System.out.println(next);
            
            if (i > 1) {
                assertEquals(current, next, "Output should stabilize after first formatting - round " + i + " differs");
            }
            
            current = next;
        }
    }
}