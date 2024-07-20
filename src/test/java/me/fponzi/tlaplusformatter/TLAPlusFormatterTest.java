package me.fponzi.tlaplusformatter;

import org.junit.jupiter.api.Test;
import tla2sany.drivers.FrontEndException;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

class TLAPlusFormatterTest {

    @Test
    void format() throws URISyntaxException, IOException, FrontEndException {
        //load file test/resources/inputs/HourClock.tla
        // format
        // compare to test/resources/outputs/HourClock.tla
        // Get the resource as a URL
        URL resource = getClass().getClassLoader().getResource("inputs/HourClock.tla");
        assertNotNull(resource, "Resource file not found");
        File input = new File(resource.toURI());

        URL outputFile = getClass().getClassLoader().getResource("outputs/HourClock.tla");
        assertNotNull(resource, "Resource file not found");
        System.out.println(outputFile);
        String expected = Files.readString(Path.of(outputFile.toURI()));
        System.out.println("Expected: " + expected);
        var f = new TLAPlusFormatter(input);
        var actual = f.getOutput();
        assertNotNull(actual, "Formatted output is null");
        assertNotNull(expected, "Expected output is null");
        assertEquals(expected, actual, "Formatted output does not match expected output");
    }


    @Test
    void testFormatModule() throws FrontEndException, IOException {
        var spec = "---- MODULE Spec ----\n======";
        var expected = "---- MODULE Spec ----\n\n======\n";
        var f = new TLAPlusFormatter(spec);
        var received = f.getOutput();
        assertEquals(expected, received, "Formatted output does not match expected output");
    }

    @Test
    void testFormatModule2() throws FrontEndException, IOException {
        var spec = "---- MODULE Spec ----\n\n======";
        var expected = "---- MODULE Spec ----\n\n======\n";
        var f = new TLAPlusFormatter(spec);
        var received = f.getOutput();
        assertEquals(expected, received, "Formatted output does not match expected output");
    }

    @Test
    void testFormatExtends() throws FrontEndException, IOException {
        var spec = "---- MODULE Spec ----\nEXTENDS Naturals\n======";
        var expected = "---- MODULE Spec ----\n\nEXTENDS Naturals\n\n======\n";
        var f = new TLAPlusFormatter(spec);
        var received = f.getOutput();
        assertEquals(expected, received, "Formatted output does not match expected output");
    }

    @Test
    void testFormatVariables() throws FrontEndException, IOException {
        var spec = "---- MODULE Spec ----\nVARIABLES x, y\n======";
        var expected = "---- MODULE Spec ----\n\nVARIABLES x, y\n\n======\n";
        var f = new TLAPlusFormatter(spec);
        var received = f.getOutput();
        assertEquals(expected, received, "Formatted output does not match expected output");
    }
}