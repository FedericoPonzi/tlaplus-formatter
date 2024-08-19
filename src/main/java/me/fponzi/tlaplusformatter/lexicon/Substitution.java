package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import me.fponzi.tlaplusformatter.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

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
        z[0].format(f); // param
        f.space();
        f.append(z[1]); // <-
        f.space();
        z[2].format(f); // expr

    }
}
