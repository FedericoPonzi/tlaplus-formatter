package me.fponzi.tlaplusformatter;

import me.fponzi.tlaplusformatter.exceptions.SanyAbortException;
import me.fponzi.tlaplusformatter.exceptions.SanyException;
import me.fponzi.tlaplusformatter.exceptions.SanySemanticException;
import me.fponzi.tlaplusformatter.exceptions.SanySyntaxException;
import org.apache.commons.io.output.WriterOutputStream;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
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
import java.lang.invoke.MethodHandles;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.Hashtable;
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
    private static String getModuleName(String spec) {
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
        // write spec to tmpfolder: TODO: take filename from module name.
        // parse spec and extract module name:
        var fileName = getModuleName(spec) + ".tla";
        File tmpFile = new File(tmpFolder, fileName);
        // Write spec to tmpFile
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
        return parseUnitContext.get(specObj.getRootModule().getName().toString()).getParseTree();
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
        LOG.debug("CONSTANTS");
        var constant = node.zero()[0].zero()[0];
        var indent = constant.getImage().length() + 1;
        f.append(constant).increaseIndent(indent).nl();

        // i=1 to skip CONSTANT[S] token
        for (int i = 1; i < node.zero().length; i++) {
            var child = node.zero()[i];
            if (child.getImage().equals(",")) {
                f.append(child).nl();
            } else {
                f.append(child.zero()[0]);
            }
        }
        f.decreaseIndent(indent).nl();
    }

    private void printVariables(TreeNode node) {
        var indent = node.zero()[0].getImage().length() + 1;
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

    // S == 1 or S(x) == x + 1
    private void printOperatorDefinition(TreeNode node) {
        var lengthCheckpoint = f.out.length();
        // node.one()[0].zero()[0] is the identifier.
        // it my be followed by parameters.
        for (var id : node.one()[0].zero()) {
            basePrintTree(id);
            for (var precomment : id.getPreComments()){
                lengthCheckpoint += precomment.length() + 1; // plus new line
            }
            if (id.getImage().equals(",")) f.space();
        }
        f.space().append(node.one()[1]); // ==
        var indentSpace = f.out.length() - lengthCheckpoint + 1; // 1 in this way the next line gets offsetted by 1 "space"
        f.increaseIndent(indentSpace)
                .nl();
        basePrintTree(node.one()[2]);
        f.decreaseIndent(indentSpace);
    }


    private void printBody(TreeNode node) {
        if (node.zero() == null) {
            // no body defined in this module.
            return;
        }
        for (var child : node.zero()) {
            //todo: move to basePrintTree
            if (child.getImage().equals("N_VariableDeclaration") && child.getKind() == 426) {
                printVariables(child);
            } else if (child.getImage().equals("N_OperatorDefinition") && child.getKind() == 389) {
                printOperatorDefinition(child);
                f.nl().nl();
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

    private void printPostfixExpr(TreeNode node) {
        basePrintTree(node.zero()[0]);
        basePrintTree(node.zero()[1]);
    }

    private void printInfixExpr(TreeNode node) {
        int lengthCheckpoint = f.out.length();
        basePrintTree(node.zero()[0]);
        f.space();
        basePrintTree(node.zero()[1]);
        f.space();
        int indentSpace = f.out.length() - lengthCheckpoint;
        f.increaseIndent(indentSpace);
        basePrintTree(node.zero()[2]);
        f.decreaseIndent(indentSpace);
    }

    private void printTheorem(TreeNode node) {
        var theoremKeyword = node.zero()[0];
        assert theoremKeyword.getImage().equals("THEOREM") && theoremKeyword.getKind() == 66;
        var indent = theoremKeyword.getImage().length() + 1;
        f.append(theoremKeyword).increaseIndent(indent).nl();
        basePrintTree(node.zero()[1]);
        f.decreaseIndent(indent).nl();
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
                // TODO: throw exception, I think this should never happen
                LOG.debug("Unhandled tree node: {}", child.getImage());
                basePrintTree(child);
            }
        }
    }

    public void printAssume(TreeNode node) {
        LOG.debug("Found ASSUME");
        var indent = "ASSUME ".length();
        f.append(node.one()[0])
                .increaseIndent(indent)
                .nl();
        basePrintTree(node.one()[1]);
        f.decreaseIndent(indent)
                .nl()
                .nl();
    }

    public void conjDisjList(TreeNode node) {
        LOG.debug("Found {}", node.getImage());
        for (int i = 0; i < node.zero().length; i++) {
            var conjDisjItem = node.zero()[i];
            conjDisjItem(conjDisjItem);
            if (i < node.zero().length - 1) {
                f.nl();
            }
        }
    }

    private void conjDisjItem(TreeNode node) {
        LOG.debug("Found {}", node.getImage());
        f.append(node.zero()[0]).space(); // "/\ "
        f.increaseIndent(3);
        basePrintTree(node.zero()[1]);
        f.decreaseIndent(3);
    }

    private void ifThenElse(TreeNode node) {
        //todo: don't append new lines if bodies have only one number or element
        var indet = "THEN ".length();
        var z = node.zero();
        var tokenIF = z[0];
        var tokenIfBody = z[1];
        var tokenThen = z[2];
        var tokenThenBody = z[3];
        var tokenElse = z[4];
        var tokenElseBody = z[5];
        f.append(tokenIF)
                .increaseIndent(indet)
                .nl();
        basePrintTree(tokenIfBody); // cond
        f.decreaseIndent(indet).nl()
                .append(tokenThen)
                .increaseIndent(indet)
                .nl();
        basePrintTree(tokenThenBody);

        f.decreaseIndent(indet).nl()
                .append(tokenElse)
                .increaseIndent(indet)
                .nl();
        basePrintTree(tokenElseBody);

        f.decreaseIndent(indet);
    }

    public void letIn(TreeNode node) {
        f.append(node.zero()[0]).
                increaseIndent(4).nl(); // LET
        for (int i = 0; i < node.zero()[1].zero().length; i++) {
            var child = node.zero()[1].zero()[i];
            basePrintTree(child);
            if (i < node.zero()[1].zero().length - 1) {
                f.nl();
            }
        }
        f.decreaseIndent(4).nl();
        f.append(node.zero()[2]); // IN
        f.increaseIndent(4).nl();
        basePrintTree(node.zero()[3]); // body
        f.decreaseIndent(4);
    }

    public void printTuple(TreeNode node) {
        var z = node.zero();
        var len = z.length;
        f.append(z[0]); // <<
        for (int i = 1; i < len - 1; i++) {
            basePrintTree(node.zero()[i]);
            if (i < node.zero().length - 2 && i % 2 == 0) {
                f.space(); // ,
            }
        }
        f.append(node.zero()[len - 1]); // >>
    }

    public void printRecursive(TreeNode node) {
        var z = node.zero();
        f.append(z[0]).space(); // RECURSIVE
        for (int i = 1; i < z.length; i++) {
            basePrintTree(z[i]);
        }
        f.nl();
    }

    public void printSubsetOf(TreeNode node) {
        var z = node.zero();
        var lengthCheckpoint = f.out.length();
        f.append(z[0]).space(); // {
        f.append(z[1]).space(); // x
        f.append(z[2]).space(); // \in
        basePrintTree(z[3]); // S
        f.append(z[4]).space(); // :
        var indent = f.out.length() - lengthCheckpoint;
        f.increaseIndent(indent);
        basePrintTree(z[5]);
        f.space().append(z[6]); // }
        f.decreaseIndent(indent);
    }

    public void printSetOfAll(TreeNode node) {
        var z = node.zero();
        f.append(z[0]).space(); // {
        basePrintTree(z[1]); // OpApplication
        f.append(z[2]).space(); // :
        basePrintTree(z[3]); // QuantBound
        f.append(z[4]); // }
    }
    // x \in S
    public void printQuantBound(TreeNode node) {
        var z = node.zero();
        var i = 0;
        // x1,x2,x3...
        while(!z[i].getImage().equals("\\in")){
            f.append(z[i]);
            if(z[i].getImage().equals(",")){
                f.space();
            }
            i++;
        }
        f.space().append(z[i]).space(); // \in
        i++;
        basePrintTree(z[i]); // S
        f.space();
    }

    // \E coef \in [1..N -> -1..1] or \A QuantBound : ConjList.
    public void printBoundedQuant(TreeNode node) {
        var z = node.zero();
        var lengthCheckpoint = f.out.length();
        f.append(z[0]).space(); // \E
        basePrintTree(z[1]); // QuantBound
        f.append(z[2]).space(); // :
        var indent = f.out.length() - lengthCheckpoint;
        f.increaseIndent(indent);
        basePrintTree(z[3]); // prop
        f.decreaseIndent(indent);
    }

    // CHOOSE e \in S: TRUE
    public void printChoose(TreeNode node) {
        var z = node.zero();
        f.append(z[0]).space(); // choose
        f.append(z[1]).space(); // var
        basePrintTree(z[2]); // maybeBound
        f.append(z[3]).space(); // :
        basePrintTree(z[4]); // condition
    }

    // "\in S" from TowerOfHanoi test.
    public void printMaybeBound(TreeNode node) {
        var z = node.zero();
        f.append(z[0]).space();
        basePrintTree(z[1]);
    }
    // A == Head(s) - it's Head(s).
    public void printOpApplication(TreeNode node) {
        var z = node.zero();
        basePrintTree(z[0]); // Head - GeneralId
        basePrintTree(z[1]); // N_OpArgs

    }
    public void printOpArgs(TreeNode node) {
        var z = node.zero();
        f.append(z[0]);
        for (int i = 1 ; i < z.length - 1 ; i++) {
            basePrintTree(z[i]);
            if (i%2 == 0) { // add space after a comma
                f.space();
            }
        }
        f.append(z[z.length - 1]);
    }
    private void printExcept(TreeNode node) {
        int lengthCheckpoint = f.out.length();
        var z = node.zero();
        f.append(z[0]); // [
        basePrintTree(z[1]); // generalId
        f.space().append(z[2]).space(); // EXCEPT
        int indentSpace = f.out.length() - lengthCheckpoint;
        f.increaseIndent(indentSpace);
        for(int i = 3; i < z.length - 1; i++) {
            basePrintTree(z[i]);
            if (i%2 == 0) { // a comma
                f.nl();
            }
        }
        f.append(z[z.length - 1]); // ]
        f.decreaseIndent(indentSpace);
    }

    // towers[from]
    private void printFcnAppl(TreeNode node) {
        basePrintTree(node.zero()[0]); // generalId.
        var o = node.one();
        f.append(o[0]); // [
        basePrintTree(o[1]);
        f.append(o[2]); // ]
    }

    public void basePrintTree(TreeNode node) {
        if (node == null) {
            return;
        }
        if (node.getImage().equals("N_ConjList") && node.getKind() == 341) {
            conjDisjList(node);
            return;
        } else if (node.getImage().equals("N_DisjList") && node.getKind() == 344) {
            conjDisjList(node);
            return;
        } else if (node.getImage().equals("N_IfThenElse") && node.getKind() == 369) {
            ifThenElse(node);
            return;
        } else if (node.getImage().equals("N_LetIn") && node.getKind() == 380) {
            letIn(node);
            return;
        } else if (node.getImage().equals("N_OperatorDefinition") && node.getKind() == 389) {
            printOperatorDefinition(node);
            return;
        } else if (node.getImage().equals("N_Theorem") && node.getKind() == 422) {
            printTheorem(node);
            return;
        } else if (node.getImage().equals("N_InfixExpr") && node.getKind() == 371) {
            printInfixExpr(node);
            return;
        } else if (node.getImage().equals("N_PostfixExpr") && node.getKind() == 395) {
            printPostfixExpr(node);
            return;
        } else if (Stream.of("EXCEPT", "UNCHANGED", "UNION", "SUBSET", "DOMAIN").anyMatch(p -> node.getImage().equals(p))) {
            // todo: handle the rest and this should fall in the default case below - print string and space
            f.append(node).space();
            return;
        } else if (node.getImage().equals("N_Tuple") && node.getKind() == 423) {
            printTuple(node);
            return;
        } else if (node.getImage().equals("N_Recursive") && node.getKind() == 431) {
            printRecursive(node);
            return;
        } else if (node.getImage().equals("N_SubsetOf") && node.getKind() == 419) {
            printSubsetOf(node);
            return;
        } else if (node.getImage().equals("N_SetOfAll") && node.getKind() == 413) {
            printSetOfAll(node);
            return;
        } else if (node.getImage().equals("N_QuantBound") && node.getKind() == 408) {
            printQuantBound(node);
            return;
        } else if (node.getImage().equals("N_BoundedQuant") && node.getKind() == 335) {
            printBoundedQuant(node);
            return;
        } else if (node.getImage().equals("N_UnBoundedOrBoundedChoose") && node.getKind() == 424) {
            printChoose(node);
            return;
        } else if (node.getImage().equals("N_MaybeBound") && node.getKind() == 381) {
            printMaybeBound(node);
            return;
        } else if(node.getImage().equals("N_GeneralId") || node.getImage().equals("N_GenPostfixOp") || node.getImage().equals("N_GenInfixOp")){
            f.append(node.zero()[1]);
            return;
        } else if(node.getImage().equals("N_OpApplication")) {
            printOpApplication(node);
            return;
        } else if(node.getImage().equals("N_OpArgs")) {
            printOpArgs(node);
            return;
        } else if (node.getImage().equals("N_FcnAppl")) {
            printFcnAppl(node);
            return;
        } else if (node.getImage().equals("N_Except")) {
            printExcept(node);
            return;
        }

        LOG.debug("Unhandled: {}", node.getImage());

        if (!node.getImage().startsWith("N_")) {
            f.append(node);
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
