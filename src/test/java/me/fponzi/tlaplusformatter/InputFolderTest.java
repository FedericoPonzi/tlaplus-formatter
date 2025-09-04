package me.fponzi.tlaplusformatter;

import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

public class InputFolderTest extends LexiconTest {
    @Test
    @Disabled
    void testPlayground() {
        testSpecFiles("Playground");
    }

    @Test
    void testFormatHourClock() {
        testSpecFiles("HourClock");
    }

    @Test
    void testRecordsWithNestedRecordsAndSequences() {
        testSpecFiles("RecordsWithNestedRecordsAndSequences");
    }

    @Test
    void testIFET() {
        testSpecFiles("IfThenElseTest");
    }

    @Test
    void testStones() {
        testSpecFiles("Stones");
    }

    @Test
    void testTowerOfHanoi() {
        testSpecFiles("TowerOfHanoi");
    }

    @Test
    @Disabled
        // TODO: fix.
    void testSlush() {
        testSpecFiles("Slush");
    }

    @Test
    void testAllConstructs() {
        testSpecFiles("AllConstructs");
    }
}
