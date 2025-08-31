package me.fponzi.tlaplusformatter;

import org.junit.jupiter.api.Test;

public class InputFolderTest extends LexiconTest {
    @Test
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
    void testSlush() {
        testSpecFiles("Slush");
    }
}
