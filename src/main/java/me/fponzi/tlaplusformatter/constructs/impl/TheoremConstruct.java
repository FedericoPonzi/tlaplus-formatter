package me.fponzi.tlaplusformatter.constructs.impl;


import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Handles THEOREM declarations.
 */
public class TheoremConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "THEOREM";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.THEOREM.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length > 0);
        var theoremName = context.buildChild(z[0]);
        var expr = context.buildChild(z[1]);
        return Doc.group(
                theoremName.appendLineOrSpace(expr)
        ).indent(z[0].getImage().length() + 1);
    }
}