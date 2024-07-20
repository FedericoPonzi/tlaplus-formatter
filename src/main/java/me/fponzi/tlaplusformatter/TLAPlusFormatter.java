package me.fponzi.tlaplusformatter;

import me.fponzi.tlaplusformatter.exceptions.SanyAbortException;
import me.fponzi.tlaplusformatter.exceptions.SanyException;
import me.fponzi.tlaplusformatter.exceptions.SanySemanticException;
import me.fponzi.tlaplusformatter.exceptions.SanySyntaxException;
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
     * <p>
     * Safety: The input spec should be called "Spec" otherwise SANY will complain.
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
        File tmpFile = new File(tmpFolder, "Spec.tla");
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
        if (node.zero() == null) {
            // no extends defined in this module.
            return;
        }
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

    private void printConstants(TreeNode node) {
        System.out.println("CONSTANTS");
        var constant = node.zero()[0].zero()[0];
        var indent = constant.getImage().length() + 1;
        f.append(constant).space().increaseIndent(indent).nl();

        // i=1 to skip CONSTANT[S] token
        for (int i = 1; i < node.zero().length; i++) {
            var child = node.zero()[i];
            if (child.getImage().equals(",")) {
                f.append(child).space().nl();
            } else {
                f.append(child.zero()[0]);
            }
        }
        f.decreaseIndent(indent).nl();
    }

    private void printVariables(TreeNode node) {
        System.err.println("Found variable.");
        var indent = node.zero()[0].getImage().length();
        f.append(node.zero()[0]); // VARIABLE
        f.increaseIndent(indent).nl();
        for (int i = 0; i < node.one().length; i++) {
            f.append(node.one()[i]);
            if (node.one()[i].getImage().equals(",") && i < node.one().length - 1) {
                f.nl();
            }
        }
        f.decreaseIndent(indent)
                .nl()
                .nl();

    }

    private void printOperatorDefinition(TreeNode node) {
        var indentSpace = node.one()[0].zero()[0].getImage().length() + " == ".length();
        f.appendSp(node.one()[0].zero()[0]) // ident
                .append(node.one()[1]) // ==
                .increaseIndent(indentSpace)
                .nl();
        basePrintTree(node.one()[2]);
        f.decreaseIndent(indentSpace);
        f.nl().nl();
    }

    private void printBody(TreeNode node) {
        if (node.zero() == null) {
            // no body defined in this module.
            return;
        }
        for (var child : node.zero()) {
            if (child.getImage().equals("N_VariableDeclaration") && child.getKind() == 426) {
                printVariables(child);
            } else if (child.getImage().equals("N_OperatorDefinition") && child.getKind() == 389) {
                printOperatorDefinition(child);
            } else if (child.getImage().startsWith("----") && child.getKind() == 35) {
                f.nl().append(child).nl().nl();
            } else if (child.getImage().equals("N_Assumption") && child.getKind() == 332) {
                printAssume(child);
            } else if (child.getImage().equals("N_ParamDeclaration") && child.getKind() == 392) {
                printConstants(child);
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
                f.append(child.zero()[0]).nl();
            } else {
                System.err.println("Unhandled node: " + node.getImage());
                basePrintTree(child);
            }
        }
    }

    public void printAssume(TreeNode node) {
        System.out.println("Found ASSUME");
        var indent = "ASSUME ".length();
        f.append(node.one()[0])
                .space()
                .increaseIndent(indent)
                .nl();
        basePrintTree(node.one()[1]);
        f.decreaseIndent(indent)
                .nl()
                .nl();
    }

    public void conjDisjList(TreeNode node) {
        System.out.println("Found conjList or DisjList");
        for (int i = 0; i < node.zero().length; i++) {
            var conjDisjItem = node.zero()[i];
            conjDisjItem(conjDisjItem);
            if (i < node.zero().length - 1) {
                f.nl();
            }
        }
    }

    private void conjDisjItem(TreeNode node) {
        f.append(node.zero()[0]).space();
        basePrintTree(node.zero()[1]);
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
        } else if (node.getImage().equals("N_ConjList") && node.getKind() == 341) {
            conjDisjList(node);
            return;
        } else if (node.getImage().equals("N_DisjList") && node.getKind() == 344) {
            conjDisjList(node);
            return;
        }
        System.out.println("Unhandled: " + node.getImage());

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
