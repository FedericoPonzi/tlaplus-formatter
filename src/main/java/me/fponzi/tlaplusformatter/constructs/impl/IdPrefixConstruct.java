package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Handles module prefixes like "R!" in "R!Nat" where R is an INSTANCE alias.
 * The prefix includes the "!" separator.
 */
public class IdPrefixConstruct implements TlaConstruct {
    @Override
    public int getSupportedNodeKind() {
        return NodeKind.ID_PREFIX.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        String image = node.getHumanReadableImage();
        if (image == null || image.isEmpty()) {
            return Doc.empty();
        }
        // Return the prefix (e.g., "R!")
        return Doc.text(image);
    }

    @Override
    public String getName() {
        return "N_IdPrefix";
    }
}
