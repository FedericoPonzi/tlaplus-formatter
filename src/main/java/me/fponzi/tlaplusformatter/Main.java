package me.fponzi.tlaplusformatter;

import ch.qos.logback.classic.LoggerContext;
import org.apache.commons.cli.*;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import tla2sany.drivers.FrontEndException;

import java.io.File;
import java.io.IOException;
import java.lang.invoke.MethodHandles;

public class Main {
    private static final Logger logger = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    private static void printHelp() {
        HelpFormatter formatter = new HelpFormatter();
        String header = "A TLA+ formatter. Use it to reformat your specs.";
        String footer = "Please contribute feedback or get the latest release from https://github.com/FedericoPonzi/tlaplus-formatter";
        formatter.printHelp("java -jar tlaplus-formatter.jar <FILE>", header, new Options(), footer, true);
    }

    //Generate
    public static void main(String[] args) throws IOException, FrontEndException {

        Options options = new Options();
        options.addOption("v", "verbosity", true, "Set the verbosity level (ERROR, WARN, INFO, DEBUG)");

        CommandLine cmd;
        try {
            // Parse the command-line arguments
            CommandLineParser parser = new DefaultParser();
            cmd = parser.parse(options, args);

            // the default log level is DEBUG.
            setLogLevel("DEBUG");
            // Set the log level based on the verbosity option
            if (cmd.hasOption("v")) {
                String verbosity = cmd.getOptionValue("v").toUpperCase();
                setLogLevel(verbosity);
            }

            // Get the remaining arguments (positional arguments)
            String[] remainingArgs = cmd.getArgs();

            if (remainingArgs.length != 1) {
                System.err.println("Please provide exactly one file path as an argument.");
                printHelp();
                System.exit(1);
            }

            // Get the file path from the positional arguments
            var file = new File(remainingArgs[0]);
            var tree = new TLAPlusFormatter(file);
            System.out.println(tree.getOutput());
        } catch (ParseException e) {
            System.err.println("Error parsing command line arguments: " + e.getMessage());
            printHelp();
            System.exit(1);
        }
    }

    private static void setLogLevel(String levelStr) {
        LoggerContext context = (LoggerContext) LoggerFactory.getILoggerFactory();
        ch.qos.logback.classic.Level level = ch.qos.logback.classic.Level.toLevel(levelStr, ch.qos.logback.classic.Level.INFO);
        context.getLogger("root").setLevel(level);
        logger.info("Log level set to {}", level);
    }
}