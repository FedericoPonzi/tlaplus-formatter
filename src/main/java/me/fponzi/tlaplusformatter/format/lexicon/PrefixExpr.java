package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

public class PrefixExpr extends TreeNode {
    public static final String IMAGE = "N_PrefixExpr";
    public static final int KIND = 399;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public PrefixExpr(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        // Example: [](A) parsed to N_GenPrefixOp N_ParenExpr
        // where [] is the GenericPrefixOperator.

        var z = this.zero();
        z[0].format(f); // prefix
        f.increaseLevel();
        z[1].format(f); // expr
        f.decreaseLevel();
    }


}
