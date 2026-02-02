package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.*;
import tla2sany.st.TreeNode;

import java.util.ArrayList;
import java.util.List;

/**
 * Construct implementation for VARIABLE/VARIABLES declarations.
 */
public class VariableConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "VARIABLES";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.VARIABLE_DECLARATION.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        Doc prefix = context.buildChild(node.zero()[0]); // "VARIABLE" or "VARIABLES" keyword

        // Extract child nodes (variable names) with their comments
        List<TreeNode> variableNodes = extractVariableNodes(node);

        if (variableNodes.isEmpty()) {
            return prefix;
        }

        // Check if any variable has comments - if so, use multi-line format
        boolean hasComments = variableNodes.stream()
                .anyMatch(n -> n.getPreComments() != null && n.getPreComments().length > 0);

        if (hasComments) {
            return formatWithComments(prefix, variableNodes, context);
        } else {
            // No comments - use simple string extraction for single-line format
            List<String> variables = context.extractStringList(node);
            return new VariableFormatter(context.getConfig()).format(prefix, variables);
        }
    }

    /**
     * Extract the variable name TreeNodes from the VARIABLES declaration.
     */
    private List<TreeNode> extractVariableNodes(TreeNode node) {
        List<TreeNode> result = new ArrayList<>();

        // Check both zero() and one() arrays for child nodes
        TreeNode[] children = null;
        if (node.one() != null && node.one().length > 0) {
            children = node.one();
        } else if (node.zero() != null && node.zero().length > 0) {
            children = node.zero();
        }

        if (children != null) {
            for (TreeNode child : children) {
                if (isValidNode(child) && child.getImage() != null) {
                    String image = child.getHumanReadableImage();
                    // Skip separators and keywords
                    if (!",".equals(image) && !"VARIABLES".equals(image) && !"VARIABLE".equals(image)) {
                        result.add(child);
                    }
                }
            }
        }

        return result;
    }

    /**
     * Check if a node is valid (not a placeholder).
     */
    private boolean isValidNode(TreeNode node) {
        return node != null &&
                node.getLocation() != null &&
                node.getLocation().beginLine() != Integer.MAX_VALUE;
    }

    /**
     * Format VARIABLES with comments preserved on separate lines.
     *
     * Note: In SANY's AST, inline comments that appear after a token (like "clock, \* comment")
     * are stored as pre-comments of the NEXT token. So "clock, \* local clock" has the comment
     * stored as a pre-comment of "req". We need to handle this by treating pre-comments of
     * variable N as post-comments of variable N-1.
     */
    private Doc formatWithComments(Doc prefix, List<TreeNode> variableNodes, ConstructContext context) {
        Doc result = prefix;
        String indent = "  "; // 2 spaces
        String commentIndent = "    "; // 4 spaces for block comments

        for (int i = 0; i < variableNodes.size(); i++) {
            TreeNode varNode = variableNodes.get(i);
            String varName = varNode.getHumanReadableImage();
            String[] preComments = varNode.getPreComments();

            if (i == 0) {
                // First variable - newline then indented name
                result = result.appendLine(Doc.text(indent + varName));
            } else {
                // Subsequent variables - add comma to previous line, then comments if any, then variable
                if (preComments != null && preComments.length > 0) {
                    // The pre-comments of this variable are actually inline comments of the previous variable
                    // Check if it's a single-line comment (\*) or multi-line block comment
                    if (preComments.length == 1 && preComments[0].trim().startsWith("\\*")) {
                        // Single inline comment: prev_var,    \* comment
                        result = result.append(Doc.text(",    " + preComments[0].trim()));
                        result = result.appendLine(Doc.text(indent + varName));
                    } else {
                        // Multi-line block comments: put comma, then each comment on its own line
                        result = result.append(Doc.text(","));
                        for (String comment : preComments) {
                            result = result.appendLine(Doc.text(commentIndent + comment.trim()));
                        }
                        result = result.appendLine(Doc.text(indent + varName));
                    }
                } else {
                    result = result.append(Doc.text(",")).appendLine(Doc.text(indent + varName));
                }
            }
        }

        return result;
    }

    /**
     * Dedicated formatter for VARIABLE declarations (without comments).
     */
    private static class VariableFormatter extends BaseConstructFormatter<String> {

        public VariableFormatter(me.fponzi.tlaplusformatter.FormatConfig config) {
            super(config);
        }

        public Doc format(Doc prefix, List<String> variables) {
            if (variables.isEmpty()) {
                return Doc.empty();
            }
            ListFormatStrategy strategy = determineStrategy("VARIABLES", variables.size());
            return formatList(variables, prefix, stringFormatter(), strategy);
        }

        @Override
        protected ListFormatStrategy determineStrategy(String constructName, int itemCount) {
            // For VARIABLES, prefer single line for short lists
            if (itemCount <= 3) {
                return ListFormatStrategy.SINGLE_LINE;
            } else {
                return config.getConstructSetting(
                        constructName, "breakStrategy", ListFormatStrategy.SMART_BREAK);
            }
        }
    }
}