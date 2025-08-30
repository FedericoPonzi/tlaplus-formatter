package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Example: ![from]=towers[from]-disk
 */
public class ExceptSpecConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_ExceptSpec";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.EXCEPT_SPEC.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null);
        var bang = context.buildChild(z[0]);
        var exceptComp = context.buildChild(z[1]);
        var eq = context.buildChild(z[2]);
        var infixExpr = context.buildChild(z[3]);
        return bang
                .append(exceptComp)
                .appendSpace(eq)
                .appendLineOrSpace(infixExpr);
    }
}
