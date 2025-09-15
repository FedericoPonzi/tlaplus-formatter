package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * So far, I've always seen this used with an empty image.
 * it's a bit annoyng because Doc.empty() will still cause an extra space to be added.
 */
public class IdPrefixConstruct implements TlaConstruct {
    @Override
    public int getSupportedNodeKind() {
        return NodeKind.ID_PREFIX.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        assert (node.getHumanReadableImage().isEmpty()); // not sure when this would not be empty
        return Doc.empty();
    }

    @Override
    public String getName() {
        return "N_IdPrefix";
    }
}
