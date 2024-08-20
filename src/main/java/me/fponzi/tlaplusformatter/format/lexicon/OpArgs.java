package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

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
            z[i].format(f);
            if (i % 2 == 0) { // add space after a comma
                f.space();
            }
        }
        f.append(z[z.length - 1]);
    }


}
