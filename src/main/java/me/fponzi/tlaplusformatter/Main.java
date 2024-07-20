package me.fponzi.tlaplusformatter;

import org.apache.commons.cli.*;
import tla2sany.drivers.FrontEndException;

import java.io.File;
import java.io.IOException;

public class Main {

    private static void printHelp() {
        HelpFormatter formatter = new HelpFormatter();
        String header = "A TLA+ formatter. Use it to reformat your specs.";
        String footer = "\n\nPath to the .tla file that contains the spec to format.";
        formatter.printHelp("java -jar TLAPlusFormatter <FILE>", header, new Options(), footer, true);
    }

    //Generate
    public static void main(String[] args) throws IOException, FrontEndException {

        Options options = new Options();

        // Add any named options here if needed in the future
        CommandLine cmd;
        try {
            // Parse the command-line arguments
            CommandLineParser parser = new DefaultParser();
            cmd = parser.parse(options, args);

            // Get the remaining arguments (positional arguments)
            String[] remainingArgs = cmd.getArgs();

            if (remainingArgs.length != 1) {
                System.err.println("Please provide exactly one file path as an argument.");
                printHelp();
                System.exit(1);
            }

            // Get the file path from the positional arguments
            File file = new File(remainingArgs[0]);
            TLAPlusFormatter tree = new TLAPlusFormatter(file);
            System.out.println(tree.getOutput());
        } catch (ParseException e) {
            System.err.println("Error parsing command line arguments: " + e.getMessage());
            printHelp();
            System.exit(1);
        }
    }
}