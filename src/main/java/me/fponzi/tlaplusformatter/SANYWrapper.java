package me.fponzi.tlaplusformatter;

import me.fponzi.tlaplusformatter.exceptions.*;
import me.fponzi.tlaplusformatter.format.FactoryRegistry;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.apache.commons.io.output.WriterOutputStream;
import tla2sany.drivers.FrontEndException;
import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.ParseUnit;
import tla2sany.modanalyzer.SpecObj;
import util.SimpleFilenameToStream;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.io.StringWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.Hashtable;

public class SANYWrapper {
    public static TreeNode load(File file) throws IOException, SanyFrontendException {
        // create a string buffer to write SANY's error messages
        // use.toString() to retrieve the error messages
        var errBuf = new StringWriter();
        var parentDirPath = file.getAbsoluteFile().getParent();
        // Resolver for filenames, patched for wired modules.
        var filenameResolver = new SimpleFilenameToStream(parentDirPath);

        // Set a unique tmpdir to avoid race-condition in SANY
        // TODO: RM once https://github.com/tlaplus/tlaplus/issues/688 is fixed
        System.setProperty("java.io.tmpdir", sanyTempDir().toString());

        var specObj = new SpecObj(file.getAbsolutePath(), filenameResolver);
        loadSpecObject(specObj, file, errBuf);
        Hashtable<String, ParseUnit> parseUnitContext = specObj.parseUnitContext;
        return FactoryRegistry.createInstance(-1, parseUnitContext.get(specObj.getRootModule().getName().toString()).getParseTree());
    }

    public static void loadSpecObject(SpecObj specObj, File file, StringWriter errBuf) throws IOException, SanyFrontendException {
        var outStream = WriterOutputStream
                .builder()
                .setWriter(errBuf)
                .setCharset(StandardCharsets.UTF_8)
                .get();

        try {
            SANY.frontEndMain(
                    specObj,
                    file.getAbsolutePath(),
                    new PrintStream(outStream)
            );
        } catch (FrontEndException e) {
            throw new SanyFrontendException(e);
        }

        ThrowOnError(specObj);
    }


    private static File sanyTempDir() throws IOException {
        return Files.createTempDirectory("sanyimp").toFile();
    }

    private static void ThrowOnError(SpecObj specObj) {
        var initErrors = specObj.getInitErrors();
        if (initErrors.isFailure()) {
            throw new SanyAbortException(initErrors.toString());
        }
        var contextErrors = specObj.getGlobalContextErrors();
        if (contextErrors.isFailure()) {
            throw new SanyAbortException(contextErrors.toString());
        }
        var parseErrors = specObj.getParseErrors();
        if (parseErrors.isFailure()) {
            throw new SanySyntaxException(parseErrors.toString());
        }
        var semanticErrors = specObj.getSemanticErrors();
        if (semanticErrors.isFailure()) {
            throw new SanySemanticException(semanticErrors.toString());
        }
        // the error level is above zero, so SANY failed for an unknown reason
        if (specObj.getErrorLevel() > 0) {
            throw new SanyException(
                    String.format("Unknown SANY error (error level=%d)", specObj.getErrorLevel())
            );
        }
    }
}
