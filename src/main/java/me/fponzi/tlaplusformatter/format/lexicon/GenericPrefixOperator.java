package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

/**
 * Examples: UNCHANGED <<1,2,3>>
 */
public class GenericPrefixOperator extends TreeNode {
    public static final String IMAGE = "N_GenPrefixOp";
    public static final int KIND = 362;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public GenericPrefixOperator(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        var z = zero();
        z[0].format(f); // this is usually `""`
        z[1].format(f); // this is the actual operator, like UNCHANGED or `~`.
        // the arguments are defined in PrefixExpr.
    }
}
