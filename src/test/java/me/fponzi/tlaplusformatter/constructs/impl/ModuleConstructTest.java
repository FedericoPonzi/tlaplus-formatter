package me.fponzi.tlaplusformatter.constructs.impl;

import me.fponzi.tlaplusformatter.TLAPlusFormatter;
import me.fponzi.tlaplusformatter.exceptions.SanyFrontendException;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class ModuleConstructTest {
    @Test
    void testDashesArePreserved() throws SanyFrontendException, IOException {
        var s = "----- MODULE m -----------\n" + "=============================";

        var f = (new TLAPlusFormatter(s)).getOutput();
        assertEquals(s, f);
    }
}
