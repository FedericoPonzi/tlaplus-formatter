package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.ArrayList;
import java.util.List;

/**
 * Construct implementation for record constructors.
 * Handles formatting of record expressions like [field1 |-> value1, field2 |-> value2].
 * See FieldValConstruct for "field1 |-> value1".
 */
public class RcdConstructorConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "RCD_CONSTRUCTOR";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.RCD_CONSTRUCTOR.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        List<Doc> fieldDocs = new ArrayList<>();
        assert (node.zero() != null && node.zero().length >= 3);
        // Process children to build field-value pairs
        // Skip first and last char - they are squared brackets, will readd them manually later.
        for (int i = 1; i < node.zero().length - 1; i++) {
            var child = node.zero()[i];
            assert (child != null);
            if (child.getHumanReadableImage().equals(",")) {
                continue;
            }
            Doc fieldDoc = context.buildChild(child);
            fieldDocs.add(fieldDoc);
        }
        // Build the record with proper formatting
        Doc content = fieldDocs.get(0);
        for (int i = 1; i < fieldDocs.size(); i++) {
            content = content.append(Doc.text(",").appendLineOrSpace(fieldDocs.get(i)));
        }
        return Doc.group(
                Doc.text("[")
                        .appendSpace(content.indent("[ ".length()))
                        .appendLineOrSpace(Doc.text("]")));
    }
}