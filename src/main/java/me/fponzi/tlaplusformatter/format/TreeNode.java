package me.fponzi.tlaplusformatter.format;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import tla2sany.st.Location;

import java.lang.invoke.MethodHandles;

public abstract class TreeNode implements Formattable {
    public tla2sany.st.TreeNode node;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    @Override
    public void format(FormattedSpec f) {
        f.append(this);
    }

    public TreeNode(tla2sany.st.TreeNode node) {
        this.node = node;
    }

    private static TreeNode[] toInternal(tla2sany.st.TreeNode[] node) {
        if(node == null) {
            return null;
        }
        TreeNode[] ret = new TreeNode[node.length];

        for (int i = 0; i < ret.length; i++) {

            ret[i] = FactoryRegistry.createInstance(node[i]);
        }
        return ret;
    }
    // If the remainder of the tree is not too long, don't add unnecessary new lines.
    public boolean shouldAddNewLine() {
        var startCol = node.getLocation().beginColumn();
        var startRow = node.getLocation().beginLine();
        var endCol = node.getLocation().endColumn();
        var endRow = node.getLocation().endLine();
        var addNewline = startRow != endRow || endCol - startCol > 50;
        return addNewline;
    }

    public TreeNode[] zero() {
        return toInternal(node.zero());
    }

    public TreeNode[] one() {
        return toInternal(node.one());
    }

    public String[] getPreComments() {
        return node.getPreComments();
    }

    public String getImage() {
        return node.getImage();
    }
    public Location getLocation() {
        return node.getLocation();
    }

    public int getKind() {
        return node.getKind();
    }
}
