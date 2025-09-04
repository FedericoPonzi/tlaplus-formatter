package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Example: `Head(s)`
 */
public class OpApplicationConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_OpApplication";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.OP_APPLICATION.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length == 2);
        //
        // z[0].format(f); // Head - GeneralId
        //z[1].format(f); // N_OpArgs
        return context.buildChild(z[0])
                .append(context.buildChild(z[1]));
    }
}
