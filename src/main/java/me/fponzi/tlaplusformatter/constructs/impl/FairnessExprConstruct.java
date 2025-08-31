package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.Arrays;
import java.util.stream.Collectors;

/**
 * Example: WF_vars(A) or SF_vars(A)
 */
public class FairnessExprConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_FairnessExpr";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.FAIRNESS_EXPR.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null);
        assert (z.length == 5); // WF_vars or SF_vars, (, var(s
        var zDocs = Arrays.stream(z).map(context::buildChild).collect(Collectors.toList());
        var collect = zDocs.get(0);
        for (int i = 1; i < zDocs.size(); i++) {
            collect = collect.append(zDocs.get(i));
        }
        return collect;
    }
}
