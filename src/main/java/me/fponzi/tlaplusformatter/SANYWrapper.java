package me.fponzi.tlaplusformatter;

import me.fponzi.tlaplusformatter.exceptions.SanyException;
import me.fponzi.tlaplusformatter.exceptions.SanyFrontendException;
import me.fponzi.tlaplusformatter.exceptions.SanySemanticException;
import me.fponzi.tlaplusformatter.exceptions.SanySyntaxException;
import tla2sany.st.TreeNode;
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
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
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
        return parseUnitContext.get(specObj.getRootModule().getName().toString()).getParseTree();
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
        private final List<String> additionalPaths;

        public CustomFilenameToStream(String parentDirPath) {
            super(parentDirPath);
            this.additionalPaths = getAdditionalModulePaths();
        }

        private static List<String> getAdditionalModulePaths() {
            List<String> paths = new ArrayList<>();
            // Check for community modules, TLAPS, and Apalache in common locations
            String[] possiblePaths = {
                // Community modules
                System.getenv("TLA_COMMUNITY_MODULES"),
                "/tmp/CommunityModules/modules",
                System.getProperty("user.home") + "/.tlaplus/CommunityModules/modules",
                // TLAPS library
                System.getenv("TLAPS_LIBRARY"),
                "/tmp/tlapm/library",
                System.getProperty("user.home") + "/.tlaplus/tlaps/library",
                "/usr/local/lib/tlaps/library",
                // Apalache modules
                System.getenv("APALACHE_HOME") != null ? System.getenv("APALACHE_HOME") + "/src/tla" : null,
                "/tmp/apalache/src/tla",
                System.getProperty("user.home") + "/.tlaplus/apalache/src/tla"
            };
            for (String path : possiblePaths) {
                if (path != null) {
                    File dir = new File(path);
                    if (dir.exists() && dir.isDirectory()) {
                        paths.add(path);
                    }
                }
            }
            return paths;
        }

        @Override
        public TLAFile resolve(String name, boolean isModule) {
            // First try with the default resolver.
            TLAFile sourceFile = super.resolve(name, isModule);
            if (sourceFile != null && sourceFile.exists()) {
                return sourceFile;
            }

            // Try additional paths (community modules, etc.)
            // name already includes .tla extension when isModule=true
            String filename = name.endsWith(".tla") ? name : name + ".tla";
            for (String path : additionalPaths) {
                File file = new File(path, filename);
                if (file.exists()) {
                    return new TLAFile(file.getAbsolutePath(), this);
                }
            }

            // Return the result from parent resolver (non-existent TLAFile, not null)
            // to preserve SANY's expected behavior
            return sourceFile;
        }
    }
}
