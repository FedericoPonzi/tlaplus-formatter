package me.fponzi.tlaplusformatter;

import org.apache.commons.io.output.WriterOutputStream;
import tla2sany.drivers.FrontEndException;
import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.ParseUnit;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.st.TreeNode;
import util.SimpleFilenameToStream;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.io.StringWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.Hashtable;

public class TLAPlusFormatter {
    // TODO: handle pre and post module comments/sections
    public FormattedSpec f;
    TreeNode root;
    public TLAPlusFormatter(File specPath) throws IOException, FrontEndException {
        root = getTreeNode(specPath.getAbsolutePath());
        format();
    }

    public String getOutput() {
        return f.getOut().toString();
    }

    /**
     * Create a new instance of the formatter from a string containing the spec.
     * The spec is written to a temporary file, which is then passed to SANY.
     * The temporary file is deleted after the formatting is complete.
     *
     * @param spec
     * @throws IOException
     */
    public TLAPlusFormatter(String spec) throws IOException, FrontEndException {
        this(storeToTmp(spec));
    }

    private static File storeToTmp(String spec) throws IOException {
        File tmpFolder = Files.createTempDirectory("sanyimp").toFile();
        // write spec to tmpfolder:
        File tmpFile = new File(tmpFolder, "spec.tla");
        // Write spec to tmpFile
        try (java.io.FileWriter writer = new java.io.FileWriter(tmpFile)) {
            writer.write(spec);
        }
        return tmpFile;
    }

    private void format() {
        f = new FormattedSpec();
        printTree(root);
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

        var ret = SANY.frontEndMain(
                specObj,
                file.getAbsolutePath(),
                new PrintStream(outStream)
        );
        if(ret != 0) {
            throw new FrontEndException(errBuf.toString());
        }
    }

    private void printBeginModule(TreeNode node) {
        f.append(node.zero()[0]) // ---- MODULE
                .space()
                .append(node.zero()[1]) // name
                .space()
                .append(node.zero()[2]) // ----
                .nl()
                .nl();
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
        var pu = parseUnitContext.get(specObj.getRootModule().getName().toString());
        return pu.getParseTree();
    }

    private void printExtends(TreeNode node) {
        f.append(node.zero()[0]) // EXTENDS
                .space();
        for (int i = 1; i < node.zero().length; i++) {
            f.append(node.zero()[i]);
            if (node.zero()[i].getImage().equals(",")) {
                f.space();
            }
        }
        f.nl().nl();
    }

    private void printVariables(TreeNode node) {
        System.err.println("Found variable.");
        f.appendSp(node.zero()[0]); // VARIABLE
        for (int i = 0; i < node.one().length; i++) {
            f.append(node.one()[i]);
            if (node.one()[i].getImage().equals(",")) {
                f.space();
            }
        }
        f.nl().nl();

    }

    private void printOperatorDefinition(TreeNode node) {
        var indentSpace = node.one()[0].zero()[0].getImage().length() + " == ".length();
        f.appendSp(node.one()[0].zero()[0]) // ident
                .append(node.one()[1]) // ==
                .increaseIndent(indentSpace)
                .nl();
        basePrintTree(node.one()[2]);
        f.decreaseIndent(indentSpace);
        f.nl();
    }

    private void printBody(TreeNode node) {
        for (var child : node.zero()) {
            if (child.getImage().equals("N_VariableDeclaration") && child.getKind() == 426) {
                printVariables(child);
            } else if (child.getImage().equals("N_OperatorDefinition") && child.getKind() == 389) {
                printOperatorDefinition(child);
            } else if (child.getImage().startsWith("----") && child.getKind() == 35) {
                f.nl().append(child).nl().nl();
            } else {
                basePrintTree(child);
            }
        }
    }

    public void printTree(TreeNode node) {
        for (var child : node.zero()) {
            if (child.getImage().equals("N_BeginModule") && child.getKind() == 333) {
                printBeginModule(child);
            } else if (child.getImage().equals("N_Extends") && child.getKind() == 350) {
                printExtends(child);
            } else if (child.getImage().equals("N_Body") && child.getKind() == 334) {
                printBody(child);
            } else if (child.getImage().equals("N_EndModule") && child.getKind() == 345) {
                f.nl().append(child.zero()[0]).nl();
            } else {
                System.err.println("Unhandled node: " + node.getImage());
                basePrintTree(child);
            }
        }
    }

    public void postfixExpr(TreeNode node) {
        f.append(node.zero()[0].zero()[1]).append(node.zero()[1].zero()[1]).space();
    }

    public void basePrintTree(TreeNode node) {
        if (node == null) {
            return;
        }
        if (node.getImage().equals("N_PostfixExpr") && node.getKind() == 395) {
            postfixExpr(node);
            return;
        }
        if (!node.getImage().startsWith("N_")) {
            f.append(node).space();
        }
        if (node.zero() != null) {
            for (var child : node.zero()) {
                basePrintTree(child);
            }
        }
        if (node.one() != null) {
            for (var child : node.one()) {
                basePrintTree(child);
            }
        }
    }
}
