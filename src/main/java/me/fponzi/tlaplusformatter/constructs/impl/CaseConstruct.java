package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

public class CaseConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_Case";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.CASE.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length >= 3);
        Doc cases = context.buildChild(z[0])
                .appendSpace(context.buildChild(z[1])); // case keyword + first case condition
        for (int i = 2; i < z.length - 1; i += 2) {
            var bracket = context.buildChild(z[i]);
            var caseArm = context.buildChild(z[i + 1]);
            cases = cases.appendLine(bracket).appendSpace(caseArm);
        }
        return cases;
    }
}
