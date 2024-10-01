package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

/**
 * Entry point for the format.
 */
public class TlaModule extends TreeNode {
    public static final String IMAGE = "N_Module";
    public static final int KIND = 382;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public TlaModule(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        if(this.zero() == null) return;
        for (var child : this.zero()) {
            child.format(f);
        }
    }
}
