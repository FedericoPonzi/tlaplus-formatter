package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.ArrayList;
import java.util.List;

// \E coef \in [1..N -> -1..1] or \A QuantBound : ConjList.
public class BoundedQuantConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "BOUNDED_QUANT";
    }

    @Override
    public int getSupportedNodeKind() {
        // N_BoundedQuant
        return NodeKind.BOUNDED_QUANT.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        var exists = context.buildChild(z[0]);
        List<Doc> elementDocs = new ArrayList<>();
        for (int i = 1; i < z.length - 2; i++) {
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
        /*
                var z = this.zero();
        f.append(z[0]).space(); // \E
        for (int i = 1; i < z.length - 2; i++) {
            z[i].format(f); // QuantBound
            if (i % 2 == 0) { // ,
                f.space();
            }
        }
        f.append(z[z.length - 2]); // :
        f.increaseLevel();
        f.space();
        z[z.length - 1].format(f); // prop
        f.decreaseLevel();
         */
        return Doc.group(
                exists.appendSpace(content)
                        .append(Doc.text(":"))
                        .appendLineOrSpace(context.buildChild(z[z.length - 1])).indent(indentSize)
        );
    }
}
