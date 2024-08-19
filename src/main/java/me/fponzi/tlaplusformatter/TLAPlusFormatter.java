package me.fponzi.tlaplusformatter;

import me.fponzi.tlaplusformatter.exceptions.SanyAbortException;
import me.fponzi.tlaplusformatter.exceptions.SanyException;
import me.fponzi.tlaplusformatter.exceptions.SanySemanticException;
import me.fponzi.tlaplusformatter.exceptions.SanySyntaxException;
import org.apache.commons.io.output.WriterOutputStream;
import org.reflections.Reflections;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import tla2sany.drivers.FrontEndException;
import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.ParseUnit;
import tla2sany.modanalyzer.SpecObj;
import util.SimpleFilenameToStream;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.io.StringWriter;
import java.lang.invoke.MethodHandles;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.Hashtable;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

public class TLAPlusFormatter {
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public FormattedSpec f;
    TreeNode root;
    File spec;

    public TLAPlusFormatter(File specPath) throws IOException, FrontEndException {
        root = getTreeNode(specPath.getAbsolutePath());
        this.spec = specPath;

        // Use Reflections library to find all classes that extend TreeNode
        Reflections reflections = new Reflections("me.fponzi.tlaplusformatter.lexicon");
        Set<Class<? extends TreeNode>> classes = reflections.getSubTypesOf(TreeNode.class);
        LOG.info("mmmmmh");
        for (Class<? extends TreeNode> clazz : classes) {
            LOG.info("Registering: {}", clazz.getCanonicalName());
            FactoryRegistry.register(clazz);
        }

        format();
    }

    public String getOutput() {
        return f.getOut().toString();
    }

    /**
     * Create a new instance of the formatter from a string containing the spec.
     * The spec is written to a temporary file, which is then passed to SANY.
     * The temporary file is deleted after the formatting is complete.
     * <p>
     * Safety: The input spec should be called "Spec" otherwise SANY will complain.
     *
     * @param spec
     * @throws IOException
     */
    public TLAPlusFormatter(String spec) throws IOException, FrontEndException {
        this(storeToTmp(spec));
    }

    static String getModuleName(String spec) {
        String regex = "----\\s?MODULE\\s+(\\w+)\\s?----";
        Pattern pattern = Pattern.compile(regex);
        Matcher matcher = pattern.matcher(spec);

        // Find the first match
        if (matcher.find()) {
            return matcher.group(1);
        } else {
            return "Spec";
        }
    }

    private static File storeToTmp(String spec) throws IOException {
        File tmpFolder = Files.createTempDirectory("sanyimp").toFile();
        var fileName = getModuleName(spec) + ".tla";
        File tmpFile = new File(tmpFolder, fileName);
        try (java.io.FileWriter writer = new java.io.FileWriter(tmpFile)) {
            writer.write(spec);
        }
        return tmpFile;
    }

    private String[] getPreAndPostModuleSections(String spec, int startLine, int endLine) {
        String[] lines = spec.split("\\R"); // Split by any line terminator
        StringBuilder preModuleSection = new StringBuilder();
        StringBuilder postModuleSection = new StringBuilder();

        for (int i = 0; i < lines.length; i++) {
            if (i < startLine - 1) {
                preModuleSection.append(lines[i]).append(System.lineSeparator());
            } else if (i > endLine - 1) {
                postModuleSection.append(lines[i]).append(System.lineSeparator());
            }
        }
        return new String[]{preModuleSection.toString(), postModuleSection.toString()};
    }

    private void format() {
        f = new FormattedSpec();
        String[] extraSections = new String[]{"", ""};
        try {
            String content = Files.readString(spec.toPath());
            //read all the content of spec:
            var startOfModuleRow = root.zero()[0].getLocation().getCoordinates()[0];
            var endOfModuleRow = root.zero()[3].getLocation().getCoordinates()[0];
            extraSections = getPreAndPostModuleSections(content, startOfModuleRow, endOfModuleRow);
        } catch (Exception e) {
            LOG.error("Failed to read content of the spec to get pre and post module sections: " + e);
        }
        f.append(extraSections[0]);
        printTree(root);
        f.append(extraSections[1]);
    }


    private static File sanyTempDir() throws IOException {
        return Files.createTempDirectory("sanyimp").toFile();
    }

    public static void loadSpecObject(SpecObj specObj, File file, StringWriter errBuf) throws IOException, FrontEndException {
        var outStream = WriterOutputStream
                .builder()
                .setWriter(errBuf)
                .setCharset(StandardCharsets.UTF_8)
                .get();

        SANY.frontEndMain(
                specObj,
                file.getAbsolutePath(),
                new PrintStream(outStream)
        );
        ThrowOnError(specObj);
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

    public TreeNode getTreeNode(String specPath) throws IOException, FrontEndException {
        var file = new File(specPath);
        // create a string buffer to write SANY's error messages
        // use.toString() to retrieve the error messages
        var errBuf = new StringWriter();
        var parentDirPath = file.getAbsoluteFile().getParent();
        // Resolver for filenames, patched for wired modules.
        var filenameResolver = new SimpleFilenameToStream(parentDirPath);

        // Set a unique tmpdir to avoid race-condition in SANY
        // TODO: RM once https://github.com/tlaplus/tlaplus/issues/688 is fixed
        System.setProperty("java.io.tmpdir", sanyTempDir().toString());

        // call SANY
        var specObj = new SpecObj(file.getAbsolutePath(), filenameResolver);
        loadSpecObject(specObj, file, errBuf);
        Hashtable<String, ParseUnit> parseUnitContext = specObj.parseUnitContext;
        return FactoryRegistry.createInstance(-1, parseUnitContext.get(specObj.getRootModule().getName().toString()).getParseTree());
    }

    private void printBody(TreeNode node) {
        if (node.zero() == null) {
            // no body defined in this module.
            return;
        }
        for (var child : node.zero()) {
            if (child.getImage().equals("N_OperatorDefinition") && child.getKind() == 389) {
                FactoryRegistry.createInstance(child.getKind(), child.node).format(f);
                f.nl().nl();
            } else if (child.getImage().startsWith("----") && child.getKind() == 35) {
                f.nl().append(child).nl().nl();
            } else if (child.getImage().equals("N_Assumption") && child.getKind() == 332) {
                FactoryRegistry.createInstance(child.getKind(), child.node).format(f);
            } else if (child.getImage().equals("N_ModuleDefinition") && child.getKind() == 383) {
                FactoryRegistry.createInstance(child.getKind(), child.node).format(f);
            } else if (child.getImage().equals("N_FunctionDefinition")) {
                FactoryRegistry.createInstance(child.getKind(), child.node).format(f);
                f.nl();
            } else {
                basePrintTree(child, this.f);
            }
        }
    }

    public void printTree(TreeNode node) {
        for (var child : node.zero()) {
            if (child.getImage().equals("N_BeginModule") && child.getKind() == 333) {
                FactoryRegistry.createInstance(child.getKind(), child.node).format(f);
            } else if (child.getImage().equals("N_Extends") && child.getKind() == 350) {
                FactoryRegistry.createInstance(child.getKind(), child.node).format(f);
            } else if (child.getImage().equals("N_EndModule") && child.getKind() == 345) {
                FactoryRegistry.createInstance(child.getKind(), child.node).format(f);
            } else if (child.getImage().equals("N_Body") && child.getKind() == 334) {
                printBody(child);
            } else {
                // TODO: throw exception, I think this should never happen
                LOG.debug("Unhandled tree node: {}", child.getImage());
                basePrintTree(child, this.f);
            }
        }
    }


    public static void basePrintTree(TreeNode node, FormattedSpec f) {
        if (node == null) {
            return;
        }
        if (Stream.of("EXCEPT", "UNCHANGED", "UNION", "SUBSET", "DOMAIN", "INSTANCE").anyMatch(p -> node.getImage().equals(p))) {
            // todo: handle the rest and this should fall in the default case below - print string and space
            f.append(node).space();
            return;
        } else if (node.getImage().equals("N_GeneralId") || node.getImage().equals("N_GenPostfixOp") || node.getImage().equals("N_GenInfixOp")) {
            // this might have as image an identifier like "Nat"
            // but also an idPrefix in pos [0] and identifier in [1], like for !Nat.
            // In this case it's easier to just delegate to basePrintTree
            for (var ch : node.zero()) {
                basePrintTree(ch, f);
            }
            return;
        } else if (List.of(
                423, 431, 419, 413, 408,
                335, 424, 381, 387, 388,
                352, 346, 356, 351, 336,
                353, 399, 363, 376, 420,
                349, 372, 426, 35, 332,
                392, 341, 344,369, 380,
                389, 422, 371, 395).contains(node.getKind())) {
            FactoryRegistry.createInstance(node.getKind(), node.node).format(f);
            return;
        }

        LOG.debug("Unhandled: {}", node.getImage());

        if (!node.getImage().startsWith("N_")) {
            f.append(node);
        }
        if (node.zero() != null) {
            for (var child : node.zero()) {
                basePrintTree(child, f);
            }
        }
        if (node.one() != null) {
            for (var child : node.one()) {
                basePrintTree(child, f);
            }
        }
    }
}
