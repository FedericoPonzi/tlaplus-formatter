package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

import static me.fponzi.tlaplusformatter.TLAPlusFormatter.basePrintTree;

public class GenericTreeNode extends TreeNode
{
    public static final int KIND = -1;
    public static final String IMAGE = "Generic";
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public GenericTreeNode(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        LOG.info("Hello generic formatter: {}, {}", node.getKind(), node.getImage());
        // TODO: while refactoring, just call baseprint tree.
        basePrintTree(this, f);
        return;
    }
}
