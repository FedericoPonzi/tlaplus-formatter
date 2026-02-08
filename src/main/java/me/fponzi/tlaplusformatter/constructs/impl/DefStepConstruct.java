package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Handles proof DEFINE steps (N_DefStep).
 *
 * Structure: zero[] = [DEFINE keyword, def1, def2, ...]
 * Each definition after the first goes on a new line, aligned under the first.
 */
public class DefStepConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "N_DefStep";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.DEF_STEP.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length >= 2);

        // z[0] = DEFINE keyword, z[1..n] = operator definitions
        Doc keyword = context.buildChild(z[0]);
        Doc defs = context.buildChild(z[1]);
        for (int i = 2; i < z.length; i++) {
            defs = defs.appendLine(context.buildChild(z[i]));
        }
        // Align definitions under the first definition (after "DEFINE ")
        return keyword.appendSpace(defs.indent(z[0].getImage().length() + 1));
    }
}
