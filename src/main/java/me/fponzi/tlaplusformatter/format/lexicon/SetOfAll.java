package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

// Example: RecordCombine(S, T) ==\n" +
//                "   {rc(s, t):s \\in S, t \\in T}
public class SetOfAll extends TreeNode {
    public static final String IMAGE = "N_SetOfAll";
    public static final int KIND = 413;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public SetOfAll(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        var z = this.zero();
        for (TreeNode treeNode : z) {
            treeNode.format(f);
            if (treeNode.getImage().equals(",")) f.space();
            if (treeNode.getImage().equals(":")) f.increaseLevel();
            if (treeNode.getImage().equals(":")) f.space();
        }
        f.decreaseLevel();
    }

}
