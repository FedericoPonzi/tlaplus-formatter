package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Handles set of records constructs.
 * Example: '[type:{TerminationMessageType},pid:SlushLoopProcess]'
 */
public class SetOfRcdsConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_SetOfRcds";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.SET_OF_RCDS.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length >= 3);
        var ret = context.buildChild(z[0]);
        for (int i = 1; i < z.length; i++) {
            var doc = context.buildChild(z[i]);
            if (z[i].getImage().equals(",")) {
                ret = ret.appendLineOrSpace(doc);
            } else {
                ret = ret.append(doc);
            }
        }
        // closing ] is included in the last child above.
        return Doc.group(ret).indent(indentSize);
    }
}
