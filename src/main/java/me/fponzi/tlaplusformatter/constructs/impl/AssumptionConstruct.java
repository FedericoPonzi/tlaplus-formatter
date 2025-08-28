package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

public class AssumptionConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_Assumption";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.ASSUMPTION.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var o = node.one();
        assert (o != null && o.length == 2);
        return Doc.group(
                Doc.text(o[0].getImage())
                        .appendSpace(context.buildChild(o[1]))
        );
    }
}
