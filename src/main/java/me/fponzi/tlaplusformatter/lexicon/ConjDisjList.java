package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import me.fponzi.tlaplusformatter.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

import static me.fponzi.tlaplusformatter.TLAPlusFormatter.basePrintTree;

public abstract class ConjDisjList extends TreeNode {
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());
    public ConjDisjList(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        LOG.debug("Found {}", this.getImage());
        for (int i = 0; i < this.zero().length; i++) {
            conjDisjItem(this.zero()[i], f);
            if (i < this.zero().length - 1) {
                f.nl();
            }
        }
    }

    // todo can be refactored to its own class
    private static void conjDisjItem(TreeNode node, FormattedSpec f) {
        LOG.debug("Found {}", node.getImage());
        f.append(node.zero()[0]); // "/\ "
        f.increaseLevel().space();
        basePrintTree(node.zero()[1], f);
        f.decreaseLevel();
    }

}















