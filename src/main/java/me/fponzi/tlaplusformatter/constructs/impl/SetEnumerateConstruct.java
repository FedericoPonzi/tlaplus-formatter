package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.ArrayList;
import java.util.List;

/**
 * Construct implementation for set enumerations.
 * Handles formatting of set expressions like {element1, element2, element3}.
 */
public class SetEnumerateConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "SET_ENUMERATE";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.SET_ENUMERATE.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        assert (node.zero() != null && node.zero().length >= 2);
        List<Doc> elementDocs = new ArrayList<>();

        // Process children to build set elements
        // Skip first and last elements - they are { and } braces
        for (int i = 1; i < node.zero().length - 1; i++) {
            TreeNode child = node.zero()[i];
            assert (child != null);
            if (child.getHumanReadableImage().equals(",")) {
                continue;
            }
            Doc elementDoc = context.buildChild(child);
            elementDocs.add(elementDoc);

        }

        if (elementDocs.isEmpty()) {
            return Doc.text("{}");
        }

        Doc content = elementDocs.get(0);
        for (int i = 1; i < elementDocs.size(); i++) {
            content = content.append(Doc.text(",")).appendLineOrSpace(elementDocs.get(i));
        }

        return Doc.group(
                context.buildChild(node.zero()[0]) // {
                        .appendSpace(content.indent("{ ".length()))
                        .appendLineOrSpace(context.buildChild(node.zero()[node.zero().length - 1])) // }
        );
    }
}