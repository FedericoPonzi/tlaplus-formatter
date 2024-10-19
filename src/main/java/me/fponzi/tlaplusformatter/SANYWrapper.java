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

import java.io.*;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.Hashtable;
import java.util.List;

public class SANYWrapper {
    public static TreeNode load(File file) throws IOException, SanyFrontendException {
        // create a string buffer to write SANY's error messages
        // use.toString() to retrieve the error messages
        var errBuf = new StringWriter();

        // Construct library lookup path
        List<String> libraryPaths = new ArrayList<>();

        // 1. Include the file's parent directory
        String parentDirPath = file.getAbsoluteFile().getParent();
        if (parentDirPath != null) {
            libraryPaths.add(parentDirPath);
        }
        URL tlapsResource = SANYWrapper.class.getClassLoader().getResource("tlaps-lib/TLAPS.tla");

        // Resolver for filenames, patched for wired modules.
        var filenameResolver = new CustomFilenameToStream(parentDirPath);

        // Set a unique tmpdir to avoid race-condition in SANY
        // TODO: RM once https://github.com/tlaplus/tlaplus/issues/688 is fixed
        System.setProperty("java.io.tmpdir", sanyTempDir().toString());

        var specObj = new SpecObj(file.getAbsolutePath(), filenameResolver);
        loadSpecObject(specObj, file, errBuf);
        Hashtable<String, ParseUnit> parseUnitContext = specObj.parseUnitContext;
        return FactoryRegistry.createInstance(parseUnitContext.get(specObj.getRootModule().getName().toString()).getParseTree());
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

    private static class CustomFilenameToStream extends SimpleFilenameToStream {
        public CustomFilenameToStream(String parentDirPath) {
            super(parentDirPath);
        }
        @Override
        public File resolve(String name, boolean isModule) {
            // First try with the default resolver.
            File sourceFile = super.resolve(name,  isModule);
            if(sourceFile != null && sourceFile.exists()){
                return sourceFile;
            }

            // If that failed, let's try to search it in the local resources:
            if (isModule) {
                // Try to load TLAPS.tla from the bundled resources
                InputStream tlapsStream = getClass().getResourceAsStream("/tlaps-lib/" +  name);
                if (tlapsStream != null) {
                    try {
                        File tempFile = File.createTempFile("TLAPS", ".tla");
                        tempFile.deleteOnExit();
                        Files.copy(tlapsStream, tempFile.toPath(), StandardCopyOption.REPLACE_EXISTING);
                        return tempFile;
                    } catch (IOException e) {
                        // If there's an error, fall back to the default behavior
                        e.printStackTrace();
                    }
                }
            }
            // At least we tried :)
            return null;
        }
    }
}
