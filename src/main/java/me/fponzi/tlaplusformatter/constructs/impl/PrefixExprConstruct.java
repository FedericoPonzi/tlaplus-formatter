package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Example: `-1`.
 */
public class PrefixExprConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_PrefixExpr";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.PREFIX_EXPR.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        var genInfixOp = context.buildChild(z[0]);
        var val = context.buildChild(z[1]);
        return Doc.group(
                genInfixOp.append(val)
        );
    }
}
