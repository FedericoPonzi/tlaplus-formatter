package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * N_OpArgs' hri: '([i\in1..N|->coef[i]*seq[i]])'
 * Chcek: N_OpApplication
 */
public class OpArgsConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "OpArgs";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.OP_ARGS.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null);
        var ret = context.buildChild(z[0]); // (
        for (int i = 1; i < z.length - 1; i++) {
            var doc = context.buildChild(z[i]);
            if (z[i].getImage().equals(",") || z[i].getImage().equals(":") || i == 1) {
                ret = ret.append(doc);
            } else {
                ret = ret.appendLineOrSpace(doc);
            }
        }
        return ret.appendLineOrEmpty(context.buildChild(z[z.length - 1])); // )
    }
}
