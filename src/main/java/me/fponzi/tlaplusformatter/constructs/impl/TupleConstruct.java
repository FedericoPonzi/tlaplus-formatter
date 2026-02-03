package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.ArrayList;
import java.util.List;

/**
 * Construct implementation for tuples.
 * Handles formatting of tuple expressions like <<element1, element2, element3>>.
 */
public class TupleConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "TUPLE";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.TUPLE.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        List<Doc> elementDocs = new ArrayList<>();
        assert (node.zero() != null && node.zero().length >= 2);

        // Check for comments on the opening << bracket
        TreeNode openBracket = node.zero()[0];
        Doc openDoc = ConstructContext.addComments(openBracket, Doc.text("<<"));

        // Skip first and last elements - they are << and >> brackets
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
            return ConstructContext.addComments(openBracket, Doc.text("<<>>"));
        }

        // Build the tuple with proper formatting
        Doc content = elementDocs.get(0);
        for (int i = 1; i < elementDocs.size(); i++) {
            content = content.append(Doc.text(",")).appendLineOrSpace(elementDocs.get(i));
        }

        return Doc.group(
                openDoc
                        .appendSpace(content.indent("<< ".length()))
                        .appendLineOrSpace(Doc.text(">>"))
        );
    }
}