package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Example: the x in `let x in y`.
 */
public class LetDefinitionsConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_LetDefinitions";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.LET_DEFINITIONS.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length > 0);
        var defs = context.buildChild(z[0]);
        for (int i = 1; i < z.length; i++) {
            defs = defs.append(Doc.text(",")).appendLineOrSpace(context.buildChild(z[i])).indent(indentSize);
        }
        return Doc.group(defs);
    }
}
