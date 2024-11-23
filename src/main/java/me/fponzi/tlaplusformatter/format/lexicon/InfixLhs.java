package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

// TODO: This is untested
// Example: R ** T in
// R ** T == LET SR == Support(x)....
public class InfixLhs extends TreeNode {
    public static final String IMAGE = "N_InfixLHS";
    public static final int KIND = 372;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public InfixLhs(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
            this.zero()[0].format(f);
            f.space();
            this.zero()[1].format(f);
            f.space();
            this.zero()[2].format(f);

    }


}
