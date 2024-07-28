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
import java.util.List;
import java.util.Objects;
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

    // Example: CONSTANTS A,B
    // Example: CONSTANT CalculateHash(_,_,_),
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
                basePrintTree(child);
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

    // Exmaple: N == INSTANCE B
    // Example: N == INSTANCE Reachable WITH vroot<-vrootBar, pc<-pcBar TODO
    private void printModuleDefinition(TreeNode node) {
        basePrintTree(node.one()[0]); // IdentLHS
        f.space().append(node.one()[1]); // ==
        f.increaseLevel().nl();
        basePrintTree(node.one()[2]); // N_NonLocalInstance.
        f.decreaseLevel().nl().nl();
    }

    // S == 1 or S(x) == x + 1
    // or a \odot b == c
    // node.one()[0].zero()[0] is (usually) the identifier.
    // node.one()[1] has the == sign.
    private void printOperatorDefinition(TreeNode node) {
        var o = node.one();
        for (int i = 0; i < o[0].zero().length; i++) {
            var ch = node.one()[0].zero()[i];
            basePrintTree(ch);
            if (i + 1 < o[0].zero().length && !(List.of(",", "(", ")").contains(o[0].zero()[i + 1].getImage())) && !Objects.equals("(", ch.getImage())) {
                f.space();
            } else if (ch.getImage().equals(",")) f.space();
        }
        f.space().append(node.one()[1]); // ==
        f.increaseLevel().nl();
        basePrintTree(node.one()[2]);
        f.decreaseLevel();
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
            } else if (child.getImage().equals("N_ModuleDefinition") && child.getKind() == 383) {
                printModuleDefinition(child);
            } else if (child.getImage().equals("N_FunctionDefinition")) {
                printFunctionDefinition(child);
                f.nl();
            } else {
                basePrintTree(child);
            }
        }
    }

    private void printPostfixExpr(TreeNode node) {
        basePrintTree(node.zero()[0]);
        basePrintTree(node.zero()[1]);
    }


    // Example: a \/ b
    private void printInfixExpr(TreeNode node) {
        basePrintTree(node.zero()[0]);
        f.space();
        basePrintTree(node.zero()[1]);
        f.increaseLevel();
        f.space();
        basePrintTree(node.zero()[2]);
        f.decreaseLevel();
    }

    // Example: R ** T in
    // R ** T == LET SR == Support(x)....
    private void printInfixLhs(TreeNode node) {
        basePrintTree(node.zero()[0]);
        f.space();
        basePrintTree(node.zero()[1]);
        f.space();
        basePrintTree(node.zero()[2]);
    }

    private void printTheorem(TreeNode node) {
        var theoremKeyword = node.zero()[0];
        assert theoremKeyword.getImage().equals("THEOREM") && theoremKeyword.getKind() == 66;
        f.append(theoremKeyword).increaseLevel().nl();
        for (int i = 1; i < node.zero().length; i++) {
            basePrintTree(node.zero()[i]);
        }
        f.decreaseLevel().nl();
    }

    // TODO: look at Queens.tla
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

    // ASSUME x > 0 or ASSUME x == /\ something
    // not sure why x == something is not parsed as Operator definition but instead it will add three nodes.
    public void printAssume(TreeNode node) {
        LOG.debug("Found ASSUME");
        var one = node.one();

        f.append(one[0])
                .increaseLevel()
                .nl();
        basePrintTree(one[1]);
        // TODO: additional isolated test
        // I think this is a bug in SANY or something unexpected on the parsing output side.
        if (one.length > 3 && one[2].getImage().equals("==")) {
            //it's an op declaration.
            // one[1] has the id
            f.space();
            basePrintTree(one[2]); // ==
            f.increaseLevel();
            f.nl();
            basePrintTree(one[3]); // content
            f.decreaseLevel();
        }
        f.decreaseLevel()
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
        f.append(node.zero()[0]); // "/\ "
        f.increaseLevel().space();
        basePrintTree(node.zero()[1]);
        f.decreaseLevel();
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
            if (i < node.zero()[1].zero().length - 1
                    && !child.getImage().equals("N_Recursive") // RECURSIVE prints its own new line.
            ) {
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
        f.append(z[0]).space(); // {
        basePrintTree(z[1]); // x or a tuple like <<r, t>>
        f.space(); //
        f.append(z[2]).space(); // \in
        basePrintTree(z[3]); // S
        f.append(z[4]); // :
        f.increaseLevel();
        f.space();
        basePrintTree(z[5]);
        f.space().append(z[6]); // }
        f.decreaseLevel();
    }

    // Example: RecordCombine(S, T) ==\n" +
    //                "   {rc(s, t):s \\in S, t \\in T}
    public void printSetOfAll(TreeNode node) {
        var z = node.zero();
        for (int i = 0; i < z.length; i++) {
            basePrintTree(z[i]);
            if (z[i].getImage().equals(",")) f.space();
            if (z[i].getImage().equals(":")) f.increaseLevel();
            if (z[i].getImage().equals(":")) f.space();
        }
        f.decreaseLevel();
    }

    // x \in S
    public void printQuantBound(TreeNode node) {
        var z = node.zero();
        var i = 0;
        // x1,x2,x3...
        while (!z[i].getImage().equals("\\in")) {
            f.append(z[i]);
            if (z[i].getImage().equals(",")) {
                f.space();
            }
            i++;
        }
        f.space().append(z[i]).space(); // \in
        i++;
        basePrintTree(z[i]); // S
    }

    // \E coef \in [1..N -> -1..1] or \A QuantBound : ConjList.
    public void printBoundedQuant(TreeNode node) {
        var z = node.zero();
        f.append(z[0]).space(); // \E
        for (int i = 1; i < z.length - 2; i++) {
            basePrintTree(z[i]); // QuantBound
            if (i % 2 == 0) { // ,
                f.space();
            }
        }
        f.append(z[z.length - 2]); // :
        f.increaseLevel();
        f.space();
        basePrintTree(z[z.length - 1]); // prop
        f.decreaseLevel();
    }

    // CHOOSE e \in S: TRUE
    public void printChoose(TreeNode node) {
        var z = node.zero();
        f.append(z[0]).space(); // choose
        f.append(z[1]).space(); // var
        basePrintTree(z[2]); // maybeBound
        f.append(z[3]); // :
        f.increaseLevel();
        f.space();
        basePrintTree(z[4]); // condition
        f.decreaseLevel();
    }

    // Example: "\in S" from TowerOfHanoi test.
    public void printMaybeBound(TreeNode node) {
        var z = node.zero();
        // Example: CHOOSE c : c \notin Color, it will create an empty MaybeBound
        if (z == null) return;
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
        for (int i = 1; i < z.length - 1; i++) {
            basePrintTree(z[i]);
            if (i % 2 == 0) { // add space after a comma
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
        for (int i = 3; i < z.length - 1; i++) {
            basePrintTree(z[i]);
            if (i % 2 == 0) { // a comma
                f.nl();
            }
        }
        f.append(z[z.length - 1]); // ]
        f.decreaseIndent(indentSpace);
    }

    // Examples: towers[from] or CR[n - 1, v]
    private void printFcnAppl(TreeNode node) {
        basePrintTree(node.zero()[0]); // generalId.
        var o = node.one();
        f.append(o[0]); // [
        for (int i = 1; i < o.length - 1; i++) {
            if (i % 2 == 0) { // comma
                f.append(o[i]).space();
            } else {
                basePrintTree(o[i]);
            }
        }
        f.append(o[o.length - 1]); // ]
    }

    //  pc = [self \in ProcSet |-> CASE self = 0 -> "TM"
    //                               [] self \in ResourceManagers -> "RM"]
    private void printFcnConst(TreeNode node) {
        var z = node.zero();
        f.append(z[0]); // [
        basePrintTree(z[1]); // QuantBound
        f.append(z[2]); // |->
        f.increaseLevel();
        f.space();
        basePrintTree(z[3]); // CASE or else
        f.append(z[4]); // ]
        f.decreaseLevel();
    }

    // Example:
    // CR[n \in Nat ,v \in S ]==IF n = 0 THEN R(s, v) ELSE
    //   \/ CR[n - 1,
    //   \/ \E u \in S : CR[n - 1, /\ R(u, v)
    private void printFunctionDefinition(TreeNode node) {
        var o = node.one();
        f.append(o[0]); // function name
        f.append(o[1]); // [
        for (int i = 2; i < o.length - 2; i++) {
            if (i % 2 == 1) { // comma
                f.append(o[i]).space();
            } else {
                basePrintTree(o[i]);
            }
        }
        f.append(o[o.length - 2]) // ==
                .increaseLevel()
                .space();
        basePrintTree(o[o.length - 1]); // Definition
        f.decreaseLevel();
    }

    private void printTimes(TreeNode node) {
        var z = node.zero();
        basePrintTree(z[0]); // X
        f.space(); //
        basePrintTree(z[1]); // \X
        f.space();
        basePrintTree(z[2]); // Y
    }

    // Example:
    // WF_vars(\E i, j \in Proc: IF i # root /\ prnt[i] = NoPrnt /\ <<j, i>> \in msg
    //                                     THEN Update(i, j)
    //                                     ELSE \/ Send(i) \/ Parent(i)
    //                                          \/ UNCHANGED <<prnt, msg, rpt>>)
    private void printFairnessExpr(TreeNode node) {
        var lengthCheckPoint = f.out.length();
        var z = node.zero();
        f.append(z[0]); // WF_
        basePrintTree(z[1]); // vars
        f.append(z[2]); // (
        var indentSpace = f.out.length() - lengthCheckPoint;
        f.increaseIndent(indentSpace);
        basePrintTree(z[3]); // expr
        f.decreaseIndent(indentSpace)
                .append(z[4]); // )
    }

    private void printCase(TreeNode node) {
        var z = node.zero();
        f.append(z[0]); // CASE
        f.space();
        f.increaseIndent(2);
        for (int i = 1; i < z.length; i++) {
            basePrintTree(z[i]);
            if (i % 2 == 1) {
                if (i < z.length - 1) {
                    f.nl();
                }
            } else {
                f.space();
            }

        }
        f.decreaseIndent(2);
    }

    public void printPrefixEpr(TreeNode node) {
        // Example: [](A) -> N_GenPrefixOp N_ParenExpr
        // where [] is the genPrefix.

        var z = node.zero();
        basePrintTree(z[0]); // prefix
        basePrintTree(z[1]); // expr
    }

    // Example: INSTANCE N WITH x<-a, y<-b
    // Example: INSTANCE N
    private void printNonLocalInstance(TreeNode node) {
        f.append(node.zero()[0]); // INSTANCE
        f.space();
        basePrintTree(node.zero()[1]); // module name
        if (node.zero().length == 2) {
            return;
        }
        f.space();
        f.append(node.zero()[2]); // WITH
        f.increaseLevel().space();
        // module parameters now, they are N_Substitution.
        for (int i = 3; i < node.zero().length; i++) {
            basePrintTree(node.zero()[i]);
            if (node.zero()[i].getImage().equals(",")) {
                f.nl();
            }
        }
        f.decreaseLevel();

    }

    private void printSubstitution(TreeNode node) {
        var z = node.zero();
        basePrintTree(z[0]); // param
        f.space();
        f.append(z[1]); // <-
        f.space();
        basePrintTree(z[2]); // expr
    }

    // Example:
    // CONSTANT CalculateHash(_,_,_)
    public void printIdentDecl(TreeNode node) {
        var z = node.zero();
        for (var ch : z) {
            f.append(ch);
        }
    }

    public void basePrintTree(TreeNode node) {
        if (node == null) {
            return;
        }
        if (node.getImage().equals("N_VariableDeclaration") && node.getKind() == 426) {
            printVariables(node);
            return;
        } else if (node.getImage().equals("N_OperatorDefinition") && node.getKind() == 389) {
            printOperatorDefinition(node);
            return;
        } else if (node.getImage().startsWith("----") && node.getKind() == 35) {
            f.nl().append(node).nl().nl();
            return;
        } else if (node.getImage().equals("N_Assumption") && node.getKind() == 332) {
            printAssume(node);
            return;
        } else if (node.getImage().equals("N_ParamDeclaration") && node.getKind() == 392) {
            printConstants(node);
            return;
        } else if (node.getImage().equals("N_ConjList") && node.getKind() == 341) {
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
        } else if (Stream.of("EXCEPT", "UNCHANGED", "UNION", "SUBSET", "DOMAIN", "INSTANCE").anyMatch(p -> node.getImage().equals(p))) {
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
        } else if (node.getImage().equals("N_GeneralId") || node.getImage().equals("N_GenPostfixOp") || node.getImage().equals("N_GenInfixOp")) {
            // this might have as image an identifier like "Nat"
            // but also an idPrefix in pos [0] and identifier in [1], like for !Nat.
            // In this case it's easier to just delegate to basePrintTree
            for (var ch : node.zero()) {
                basePrintTree(ch);
            }
            return;
        } else if (node.getImage().equals("N_OpApplication")) {
            printOpApplication(node);
            return;
        } else if (node.getImage().equals("N_OpArgs")) {
            printOpArgs(node);
            return;
        } else if (node.getImage().equals("N_FcnAppl")) {
            printFcnAppl(node);
            return;
        } else if (node.getImage().equals("N_Except")) {
            printExcept(node);
            return;
        } else if (node.getImage().equals("N_FunctionDefinition")) {
            printFunctionDefinition(node);
            return;
        } else if (node.getImage().equals("N_InfixLHS")) {
            printInfixLhs(node);
            return;
        } else if (node.getImage().equals("N_Times")) {
            printTimes(node);
            return;
        } else if (node.getImage().equals("N_FairnessExpr")) {
            printFairnessExpr(node);
            return;
        } else if (node.getImage().equals("N_Case")) {
            printCase(node);
            return;
        } else if (node.getImage().equals("N_FcnConst") && node.getKind() == 353) {
            printFcnConst(node);
            return;
        } else if (node.getImage().equals("N_PrefixExpr") && node.getKind() == 399) {
            printPrefixEpr(node);
            return;
        } else if (node.getImage().equals("N_IdentDecl") && node.getKind() == 363) {
            printIdentDecl(node);
            return;
        } else if (node.getImage().equals("N_NonLocalInstance") && node.getKind() == 376) {
            printNonLocalInstance(node);
            return;
        } else if (node.getImage().equals("N_Substitution") && node.getKind() == 420) {
            printSubstitution(node);
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
