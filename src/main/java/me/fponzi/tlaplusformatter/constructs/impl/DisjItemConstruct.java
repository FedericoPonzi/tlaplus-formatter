package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

public class DisjItemConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_DisjItem";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.DISJ_ITEM.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length == 2);
        var symbol = context.buildChild(z[0]);
        var symbolLength = z[0].getImage().length() + 1;
        var expr = context.buildChild(z[1]);
        return Doc.group(
                symbol.appendSpace(expr.indent(symbolLength))
        );
    }
}
