package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

public abstract class ConjDisjList extends TreeNode {
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());
    public ConjDisjList(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        for (int i = 0; i < this.zero().length; i++) {
            conjDisjItem(this.zero()[i], f);
            if (i < this.zero().length - 1) {
                f.nl();
            }
        }
    }

    // todo can be refactored to its own class
    private static void conjDisjItem(TreeNode node, FormattedSpec f) {
        f.append(node.zero()[0]); // "/\ "
        f.increaseLevel().space();
        node.zero()[1].format(f);
        f.decreaseLevel();
    }

}















