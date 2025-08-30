package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

public class ExceptComponentConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_ExceptComponent";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.EXCEPT_COMPONENT.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length >= 3);
        return Doc.group(
                context.buildChild(z[0])
                        .append(context.buildChild(z[1]))
                        .append(context.buildChild(z[2]))
        );
    }
}
