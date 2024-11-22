package me.fponzi.tlaplusformatter.format;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import tla2sany.st.Location;

import java.lang.invoke.MethodHandles;
import java.util.Arrays;

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
        // todo: memoize.
        return toInternal(node.zero());
    }

    public TreeNode[] one() {
        return toInternal(node.one());
    }

    public String[] getPreComments() {
        return node.getPreComments();
    }

    /**
     * Get the number of pre comment lines, by recursively searching them in the first child.
     * It's used in the format method to respect the newlines between different declarations
     * in the module's body.
     * @return the number of preComments, recursively.
     */
    public int getPreCommentsSmart() {
        return getPreCommentsRec(this);
    }

    private static int getPreCommentsRec(TreeNode node) {
        if(node.getPreComments().length > 0) {
            // Each entry in PreComments is either a single line comments or a block comment.
            // Block comments are composed of multiple lines, so we need to count them all.
            // TODO: AND single line comments only include a single \n even if there is \* comment\n\n\n\n\n\n=======
            // would be great to fix this in SANY.
            // Alternatively we would need to run a new parsing of the spec, find the actual number of new lines between every line comment and
            // apply them as expected.
            return Arrays.stream(node.getPreComments())
                    .mapToInt(s -> Math.toIntExact(s.lines().count()))
                    .sum();
        }

        if(node.zero() != null && node.zero().length > 0) return getPreCommentsRec(node.zero()[0]);
        if(node.one() != null && node.one().length > 0) return getPreCommentsRec(node.one()[0]);
        return 0;
    }

    public String getImage() {
        return node.getImage();
    }
    public int getBeginLineSkipComments() {
        return node.getLocation().beginLine() - getPreCommentsSmart();
    }
    public Location getLocation() {
        return node.getLocation();
    }

    public int getKind() {
        return node.getKind();
    }
}
