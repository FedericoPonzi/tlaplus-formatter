package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.*;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import tla2sany.st.TreeNode;

import java.lang.invoke.MethodHandles;
import java.util.ArrayList;
import java.util.List;

/**
 * Construct implementation for CONSTANTS declarations.
 * Handles formatting of "CONSTANTS x, y, z" constructs.
 */
public class ConstantsConstruct implements TlaConstruct {
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    @Override
    public String getName() {
        return "N_ParamDeclaration";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.PARAM_DECLARATION.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        Doc prefix = context.buildChild(node.zero()[0]); // "CONSTANT" or "CONSTANTS" keyword

        // Extract child nodes (constant names) with their comments
        List<TreeNode> constantNodes = extractConstantNodes(node);

        if (constantNodes.isEmpty()) {
            return prefix;
        }

        // Check if any constant has comments - if so, use multi-line format
        // Comments are on the inner identifier node for IDENT_DECL nodes
        boolean hasComments = constantNodes.stream()
                .anyMatch(n -> {
                    TreeNode commentNode = getCommentNode(n);
                    return commentNode.getPreComments() != null && commentNode.getPreComments().length > 0;
                });

        if (hasComments) {
            return formatWithComments(prefix, constantNodes, context);
        } else {
            // No comments - use simple string extraction for single-line format
            List<String> constants = context.extractStringList(node);
            return new ConstantsFormatter(context.getConfig()).format(prefix, constants);
        }
    }

    /**
     * Extract the constant name TreeNodes from the CONSTANTS declaration.
     * For CONSTANT declarations, the structure is:
     * - zero[0]: CONSTANT keyword (kind=342)
     * - zero[1]: IDENT_DECL wrapper (kind=363) containing the actual identifier
     * - zero[2]: comma
     * - etc.
     *
     * The comments are attached to the identifier INSIDE the IDENT_DECL, not on the
     * IDENT_DECL wrapper itself. So we need to return the inner node for comment checking.
     */
    private List<TreeNode> extractConstantNodes(TreeNode node) {
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
                    if (!",".equals(image) && !"CONSTANTS".equals(image) && !"CONSTANT".equals(image)) {
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
     * Format CONSTANTS with comments preserved on separate lines.
     *
     * Note: In SANY's AST, inline comments that appear after a token (like "Jug, \* comment")
     * are stored as pre-comments of the NEXT token. So "Jug, \* The set" has the comment
     * stored as a pre-comment of "Capacity". We need to handle this by treating pre-comments of
     * constant N as post-comments of constant N-1.
     */
    private Doc formatWithComments(Doc prefix, List<TreeNode> constantNodes, ConstructContext context) {
        Doc result = prefix;
        String indent = "         "; // Align with "CONSTANT " (9 spaces)
        String commentIndent = "    "; // 4 spaces for block comments

        for (int i = 0; i < constantNodes.size(); i++) {
            TreeNode constNode = constantNodes.get(i);
            // Build the constant declaration string manually to avoid comment duplication
            String constDecl = buildConstantDeclaration(constNode);
            // Get comments from the inner identifier node
            TreeNode commentNode = getCommentNode(constNode);
            String[] preComments = commentNode.getPreComments();

            if (i == 0) {
                // First constant - check for comments BEFORE the constant
                if (preComments != null && preComments.length > 0) {
                    // Comments before first constant: put on separate lines
                    for (String comment : preComments) {
                        result = result.appendLine(Doc.text(commentIndent + normalizeCommentWhitespace(comment)));
                    }
                    result = result.appendLine(Doc.text(commentIndent + constDecl));
                } else {
                    // No comments - space after keyword then declaration
                    result = result.append(Doc.text(" " + constDecl));
                }
            } else {
                // Subsequent constants - add comma to previous line, then comments if any, then constant
                if (preComments != null && preComments.length > 0) {
                    // The pre-comments of this constant are actually inline comments of the previous constant
                    // Check if it's a single-line comment (\*) or multi-line block comment
                    String normalizedFirst = normalizeCommentWhitespace(preComments[0]);
                    if (preComments.length == 1 && normalizedFirst.startsWith("\\*")) {
                        // Single inline comment: prev_const,    \* comment
                        result = result.append(Doc.text(",    " + normalizedFirst));
                        result = result.appendLine(Doc.text(indent + constDecl));
                    } else {
                        // Multi-line block comments: put comma, then each comment on its own line
                        result = result.append(Doc.text(","));
                        for (String comment : preComments) {
                            result = result.appendLine(Doc.text(commentIndent + normalizeCommentWhitespace(comment)));
                        }
                        result = result.appendLine(Doc.text(indent + constDecl));
                    }
                } else {
                    result = result.append(Doc.text(",")).appendLine(Doc.text(indent + constDecl));
                }
            }
        }

        return result;
    }

    /**
     * Build the constant declaration string including operator parameters.
     * For simple constants, returns the name. For operator constants like Op(_,_),
     * returns the full declaration with parameters.
     */
    private String buildConstantDeclaration(TreeNode node) {
        // For IDENT_DECL nodes (kind=363), check for operator parameters
        if (node.getKind() == 363) {
            TreeNode[] children = node.zero();
            if (children != null && children.length > 1) {
                // Has parameters - build the full declaration
                StringBuilder sb = new StringBuilder();
                for (TreeNode child : children) {
                    if (child != null && child.getImage() != null) {
                        sb.append(child.getHumanReadableImage());
                    }
                }
                return sb.toString();
            } else if (children != null && children.length == 1) {
                return children[0].getHumanReadableImage();
            }
        }
        return node.getHumanReadableImage();
    }

    /**
     * Get the node that contains comments for a constant declaration.
     * For IDENT_DECL nodes (kind=363), comments are on the inner identifier.
     */
    private TreeNode getCommentNode(TreeNode node) {
        if (node.getKind() == 363 && node.zero() != null && node.zero().length > 0) {
            return node.zero()[0];
        }
        return node;
    }

    /**
     * Dedicated formatter for CONSTANTS declarations (without comments).
     */
    private static class ConstantsFormatter extends BaseConstructFormatter<String> {

        public ConstantsFormatter(me.fponzi.tlaplusformatter.FormatConfig config) {
            super(config);
        }

        public Doc format(Doc prefix, List<String> constants) {
            if (constants.isEmpty()) {
                return Doc.empty();
            }
            ListFormatStrategy strategy = determineStrategy("CONSTANTS", constants.size());
            return formatList(constants, prefix, stringFormatter(), strategy);
        }

        @Override
        protected ListFormatStrategy determineStrategy(String constructName, int itemCount) {
            // For CONSTANTS, use smart breaks for longer lists
            if (itemCount <= 3) {
                return ListFormatStrategy.SINGLE_LINE;
            } else {
                return config.getConstructSetting(
                        constructName, "breakStrategy", ListFormatStrategy.SMART_BREAK);
            }
        }
    }

    /**
     * Strip leading whitespace and trailing newlines from a comment,
     * but preserve trailing spaces before the newline.
     */
    private static String normalizeCommentWhitespace(String s) {
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
