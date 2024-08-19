package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import me.fponzi.tlaplusformatter.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

import static me.fponzi.tlaplusformatter.TLAPlusFormatter.basePrintTree;

public class Recursive extends TreeNode {
    public static final String IMAGE = "N_Recursive";
    public static final int KIND = 431;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public Recursive(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        var z = this.zero();
        f.append(z[0]).space(); // RECURSIVE
        for (int i = 1; i < z.length; i++) {
            basePrintTree(z[i], f);
        }
        f.nl();
    }
}
