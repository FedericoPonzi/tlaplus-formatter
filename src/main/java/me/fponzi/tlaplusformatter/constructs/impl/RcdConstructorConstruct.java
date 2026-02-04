package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

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
        // Track comma preComments by field index so we can preserve comma-first style
        Map<Integer, String[]> commaComments = new HashMap<>();
        int fieldIndex = 0;
        for (int i = 1; i < node.zero().length - 1; i++) {
            var child = node.zero()[i];
            assert (child != null);
            if (child.getHumanReadableImage().equals(",")) {
                String[] preComments = child.getPreComments();
                if (preComments != null && preComments.length > 0) {
                    commaComments.put(fieldIndex, preComments);
                }
                continue;
            }
            Doc fieldDoc = context.buildChild(child);
            fieldDocs.add(fieldDoc);
            fieldIndex++;
        }
        // Build the record with proper formatting
        Doc content = fieldDocs.get(0);
        for (int i = 1; i < fieldDocs.size(); i++) {
            String[] comments = commaComments.get(i);
            if (comments != null) {
                // Comma-first: preserve comment on comma so SANY re-attaches it correctly
                for (String comment : comments) {
                    content = content.appendLine(Doc.text(normalizeComment(comment)));
                }
                content = content.appendLine(Doc.text(", ").append(fieldDocs.get(i)));
            } else {
                content = content.append(Doc.text(",").appendLineOrSpace(fieldDocs.get(i)));
            }
        }
        return Doc.group(
                Doc.text("[")
                        .appendSpace(content.indent("[ ".length()))
                        .appendLineOrSpace(Doc.text("]")));
    }

    private static String normalizeComment(String s) {
        int start = 0;
        while (start < s.length() && Character.isWhitespace(s.charAt(start))) {
            start++;
        }
        int end = s.length();
        while (end > start && (s.charAt(end - 1) == '\n' || s.charAt(end - 1) == '\r')) {
            end--;
        }
        return s.substring(start, end);
    }
}