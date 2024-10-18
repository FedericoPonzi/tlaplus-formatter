package me.fponzi.tlaplusformatter;

import ch.qos.logback.classic.LoggerContext;
import me.fponzi.tlaplusformatter.exceptions.SanyFrontendException;
import org.apache.commons.cli.*;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.File;
import java.io.IOException;
import java.lang.invoke.MethodHandles;
import java.nio.file.Files;

public class Main {
    private static final Logger logger = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());
    private static final String VERBOSITY_OPTION = "v";
    private static final String DEFAULT_VERBOSITY_OPTION = "INFO";
    public static final String ERROR_NOT_ENOUGH_ARGS = "Please provide one or two file paths (input and optionally output) as arguments.";
    private static void printHelp() {
        HelpFormatter formatter = new HelpFormatter();
        String header = "A TLA+ formatter. Use it to reformat your specs.";
        String footer = "Please contribute feedback or get the latest release from https://github.com/FedericoPonzi/tlaplus-formatter";
        formatter.printHelp("java -jar tlaplus-formatter.jar <FILE>", header, new Options(), footer, true);
    }

    public static int mainWrapper(String[] args) {
        Options options = new Options();
        options.addOption(VERBOSITY_OPTION, "verbosity", true, "Set the verbosity level (ERROR, WARN, *INFO, DEBUG)");

        CommandLine cmd;
        try {
            // Parse the command-line arguments
            CommandLineParser parser = new DefaultParser();
            cmd = parser.parse(options, args);

            // Set the default log level to INFO
            setLogLevel(DEFAULT_VERBOSITY_OPTION);

            // Set the log level based on the verbosity option
            if (cmd.hasOption(VERBOSITY_OPTION)) {
                String verbosity = cmd.getOptionValue(VERBOSITY_OPTION).toUpperCase();
                try {
                    setLogLevel(verbosity);
                } catch (IllegalArgumentException e) {
                    logger.error("Invalid log level: {}", verbosity);
                    printHelp();
                    return 1;
                }
            }

            // Get the remaining arguments (positional arguments)
            String[] remainingArgs = cmd.getArgs();

            if (remainingArgs.length == 0 || remainingArgs.length > 2) {
                logger.error("Please provide one or two file paths (input and optionally output) as arguments.");
                printHelp();
                return 1;
            }

            // Get the input file path from the positional arguments
            File inputFile = new File(remainingArgs[0]);
            if (!inputFile.exists()) {
                logger.error("Input file does not exist: {}", inputFile.getAbsolutePath());
                return 1;
            }

            TLAPlusFormatter formatter = new TLAPlusFormatter(inputFile);
            String formattedOutput = formatter.getOutput();

            if (remainingArgs.length == 2) {
                // If output file is specified, write to the file
                File outputFile = new File(remainingArgs[1]);
                Files.writeString(outputFile.toPath(), formattedOutput);
                logger.info("Formatted output written to: {}", outputFile.getAbsolutePath());
            } else {
                // If no output file is specified, print to stdout
                System.out.println(formattedOutput);
            }

        } catch (ParseException e) {
            logger.error("Error parsing command line arguments: {}", e.getMessage());
            printHelp();
            return 1;
        } catch (IOException | SanyFrontendException e) {
            logger.error("An error occurred while processing the file: {}", e.getMessage());
            return 1;
        }
        return 0;
    }

    public static void main(String[] args) {
        System.exit(mainWrapper(args));
    }

    private static void setLogLevel(String levelStr) {
        LoggerContext context = (LoggerContext) LoggerFactory.getILoggerFactory();
        ch.qos.logback.classic.Level level = ch.qos.logback.classic.Level.toLevel(levelStr, ch.qos.logback.classic.Level.INFO);
        context.getLogger("root").setLevel(level);
        logger.debug("Log level set to {}", level);
    }
}