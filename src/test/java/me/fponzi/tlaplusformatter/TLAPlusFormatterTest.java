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
        assertEquals(actual, expected, "Formatted output does not match expected output");

    }
}