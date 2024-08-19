package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import me.fponzi.tlaplusformatter.TreeNode;

import java.lang.invoke.MethodHandles;

import static me.fponzi.tlaplusformatter.TLAPlusFormatter.basePrintTree;

public class IfThenElse extends TreeNode {
    public static final String IMAGE = "N_IfThenElse";
    public static final int KIND = 369;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public IfThenElse(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        //todo: don't append new lines if bodies have only one number or element
        var indet = "THEN ".length();
        var z = this.zero();
        var tokenIF = z[0];
        var tokenIfBody = z[1];
        var tokenThen = z[2];
        var tokenThenBody = z[3];
        var tokenElse = z[4];
        var tokenElseBody = z[5];
        f.append(tokenIF)
                .increaseIndent(indet)
                .nl();
        basePrintTree(tokenIfBody, f); // cond
        f.decreaseIndent(indet).nl()
                .append(tokenThen)
                .increaseIndent(indet)
                .nl();
        basePrintTree(tokenThenBody, f);

        f.decreaseIndent(indet).nl()
                .append(tokenElse)
                .increaseIndent(indet)
                .nl();
        basePrintTree(tokenElseBody, f);

        f.decreaseIndent(indet);

    }


}
