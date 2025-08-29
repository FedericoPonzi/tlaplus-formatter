package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Construct implementation for generic infix operators.
 * Handles formatting of infix operators like :>, @@, etc.
 */
public class GenInfixOpConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "GEN_INFIX_OP";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.GEN_INFIX_OP.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        return Doc.text(node.getHumanReadableImage());
    }
}