package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import me.fponzi.tlaplusformatter.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

import static me.fponzi.tlaplusformatter.TLAPlusFormatter.basePrintTree;

public class Substitution extends TreeNode {
    public static final String IMAGE = "N_Substitution";
    public static final int KIND = 420;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public Substitution(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        var z = this.zero();
        basePrintTree(z[0], f); // param
        f.space();
        f.append(z[1]); // <-
        f.space();
        basePrintTree(z[2], f); // expr

    }
}
