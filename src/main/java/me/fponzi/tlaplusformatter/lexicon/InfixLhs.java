package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import me.fponzi.tlaplusformatter.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

import static me.fponzi.tlaplusformatter.TLAPlusFormatter.basePrintTree;

// Example: R ** T in
// R ** T == LET SR == Support(x)....
public class InfixLhs extends TreeNode {
    public static final String IMAGE = "N_InfixLHS";
    // TODO:
    public static final int KIND = 372;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public InfixLhs(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
            basePrintTree(this.zero()[0], f);
            f.space();
            basePrintTree(this.zero()[1], f);
            f.space();
            basePrintTree(this.zero()[2], f);

    }


}
