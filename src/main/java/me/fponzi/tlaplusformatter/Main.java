package me.fponzi.tlaplusformatter;

import tla2sany.drivers.FrontEndException;

import java.io.File;
import java.io.IOException;

public class Main {
    public static void main(String[] args) throws IOException, FrontEndException {
        var file = new File("/home/fponzi/dev/tla+/tlaplus-formatter/src/test/resources/HourClock.tla");
        var tree = new TLAPlusFormatter(file);
        System.out.println("Final result:");
        System.out.println(tree.getOutput());
    }
}