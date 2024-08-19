package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import me.fponzi.tlaplusformatter.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

import static me.fponzi.tlaplusformatter.TLAPlusFormatter.basePrintTree;

// A == Head(s) - it's Head(s).
public class OpApplication extends TreeNode {
    public static final String IMAGE = "N_OpApplication";
    public static final int KIND = 387;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public OpApplication(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        var z = this.zero();
        basePrintTree(z[0], f); // Head - GeneralId
        basePrintTree(z[1], f); // N_OpArgs
    }
}
