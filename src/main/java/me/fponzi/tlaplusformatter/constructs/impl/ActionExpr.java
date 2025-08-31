package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Exmaple: `[Next]_vars`
 */
public class ActionExpr implements TlaConstruct {
    @Override
    public String getName() {
        return "N_ActionExpr";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.ACTION_EXPR.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length == 4);
        return context.buildChild(z[0]) // [
                .append(context.buildChild(z[1])) // GeneralIdentifier
                .append(context.buildChild(z[2])) // ]_
                .append(context.buildChild(z[3])); // GeneralIdentifier
    }
}
