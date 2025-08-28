package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.ArrayList;
import java.util.List;

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
        var docs = new ArrayList<Doc>();
        var open = context.buildChild(z[0]);
        var close = context.buildChild(z[z.length - 1]);
        List<Doc> elementDocs = new ArrayList<>();
        for (int i = 1; i < z.length - 1; i++) {
            TreeNode child = z[i];
            assert (child != null);
            if (child.getHumanReadableImage().equals(",")) {
                continue;
            }
            Doc elementDoc = context.buildChild(child);
            elementDocs.add(elementDoc);
        }

        Doc content = elementDocs.get(0);
        for (int i = 1; i < elementDocs.size(); i++) {
            content = content.append(Doc.text(",")).appendLineOrSpace(elementDocs.get(i));
        }

        return Doc.group(
                open
                        .appendLineOrEmpty(content.indent(indentSize))
                        .appendLineOrEmpty(close));
    }
}
