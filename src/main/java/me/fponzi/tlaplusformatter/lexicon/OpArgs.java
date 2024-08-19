package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import me.fponzi.tlaplusformatter.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

import static me.fponzi.tlaplusformatter.TLAPlusFormatter.basePrintTree;

public class OpArgs extends TreeNode {
    public static final String IMAGE = "N_OpArgs";
    public static final int KIND = 388;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public OpArgs(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        var z = this.zero();
        f.append(z[0]);
        for (int i = 1; i < z.length - 1; i++) {
            basePrintTree(z[i], f);
            if (i % 2 == 0) { // add space after a comma
                f.space();
            }
        }
        f.append(z[z.length - 1]);
    }


}
