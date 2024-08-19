package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import me.fponzi.tlaplusformatter.TreeNode;
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
        // Example: [](A) -> N_GenPrefixOp N_ParenExpr
        // where [] is the genPrefix.

        var z = this.zero();
        z[0].format(f); // prefix
        z[1].format(f); // expr
    }


}
