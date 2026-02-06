package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.TlaDocBuilder;
import me.fponzi.tlaplusformatter.constructs.*;
import tla2sany.st.TreeNode;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Construct implementation for EXTENDS declarations.
 * Handles formatting of module import lists with smart line breaking.
 */
public class ExtendsConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "EXTENDS";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.EXTENDS.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        TreeNode[] children = node.zero();
        Doc prefix = context.buildChild(children[0]); // "EXTENDS" keyword

        // Extract module name nodes (not just strings) to preserve comments
        List<TreeNode> moduleNodes = extractModuleNodes(node);
        // Extract comments from comma separators
        Map<Integer, String[]> commaComments = extractCommaPreComments(node);

        if (moduleNodes.isEmpty()) {
            return prefix;
        }

        // Check if any module node or comma has comments
        boolean hasComments = !commaComments.isEmpty() || moduleNodes.stream()
                .anyMatch(n -> n.getPreComments() != null && n.getPreComments().length > 0);

        if (hasComments) {
            return formatWithComments(prefix, moduleNodes, commaComments);
        }

        // No comments - use simple string extraction for standard formatting
        List<String> modules = new ArrayList<>();
        for (TreeNode moduleNode : moduleNodes) {
            modules.add(TlaDocBuilder.getBestImage(moduleNode));
        }
        return new ExtendsFormatter(context.getConfig()).format(prefix, modules);
    }

    /**
     * Extract module name TreeNodes from the EXTENDS declaration.
     */
    private List<TreeNode> extractModuleNodes(TreeNode node) {
        List<TreeNode> result = new ArrayList<>();
        TreeNode[] children = node.zero();
        if (children != null) {
            for (TreeNode child : children) {
                String image = TlaDocBuilder.getBestImage(child);
                if (image != null && !image.equals("EXTENDS") && !image.equals(",")) {
                    result.add(child);
                }
            }
        }
        return result;
    }

    /**
     * Extract preComments from comma separator nodes.
     * In SANY, inline comments after a module name end up as preComments of
     * the following comma. Returns a map from module index to comma preComments.
     */
    private Map<Integer, String[]> extractCommaPreComments(TreeNode node) {
        Map<Integer, String[]> result = new HashMap<>();
        TreeNode[] children = node.zero();
        if (children == null) return result;

        int moduleIndex = -1;
        for (TreeNode child : children) {
            String image = TlaDocBuilder.getBestImage(child);
            if (image == null) continue;
            if (",".equals(image)) {
                String[] comments = child.getPreComments();
                if (comments != null && comments.length > 0) {
                    result.put(moduleIndex + 1, comments);
                }
            } else if (!"EXTENDS".equals(image)) {
                moduleIndex++;
            }
        }
        return result;
    }

    /**
     * Format EXTENDS with comments preserved.
     * Uses multi-line format with alignment under the first module name.
     */
    private Doc formatWithComments(Doc prefix, List<TreeNode> moduleNodes, Map<Integer, String[]> commaComments) {
        Doc result = prefix;
        String indent = "        "; // 8 spaces to align under first module after "EXTENDS "

        for (int i = 0; i < moduleNodes.size(); i++) {
            TreeNode moduleNode = moduleNodes.get(i);
            String moduleName = TlaDocBuilder.getBestImage(moduleNode);
            String[] preComments = moduleNode.getPreComments();
            boolean isLast = (i == moduleNodes.size() - 1);

            if (i == 0) {
                if (preComments != null && preComments.length > 0) {
                    for (String comment : preComments) {
                        result = result.appendLine(Doc.text(indent + normalizeCommentWhitespace(comment)));
                    }
                    result = result.appendLine(Doc.text(indent + moduleName + (isLast ? "" : ",")));
                } else {
                    result = result.append(Doc.text(" " + moduleName + (isLast ? "" : ",")));
                }
            } else {
                if (preComments != null && preComments.length > 0) {
                    // Pre-comments on this module are inline comments of the previous module
                    String normalizedFirst = normalizeCommentWhitespace(preComments[0]);
                    if (preComments.length == 1 && normalizedFirst.startsWith("\\*")) {
                        // Line comment: append inline after previous module's comma
                        result = result.append(Doc.text(" " + normalizedFirst));
                    } else {
                        // Block comment(s): put on separate lines
                        for (String comment : preComments) {
                            result = result.appendLine(Doc.text(indent + normalizeCommentWhitespace(comment)));
                        }
                    }
                    result = result.appendLine(Doc.text(indent + moduleName + (isLast ? "" : ",")));
                } else {
                    result = result.appendLine(Doc.text(indent + moduleName + (isLast ? "" : ",")));
                }
            }

            // Handle comma post-comments (comments on the comma after this module)
            String[] postComments = commaComments.get(i + 1);
            if (postComments != null && postComments.length > 0) {
                String normalized = normalizeCommentWhitespace(postComments[0]);
                if (postComments.length == 1 && normalized.startsWith("\\*")) {
                    result = result.append(Doc.text(" " + normalized));
                } else {
                    for (String comment : postComments) {
                        result = result.append(Doc.text(" " + normalizeCommentWhitespace(comment)));
                    }
                }
            }
        }

        return result;
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

    /**
     * Dedicated formatter for EXTENDS declarations (without comments).
     */
    private static class ExtendsFormatter extends BaseConstructFormatter<String> {

        public ExtendsFormatter(me.fponzi.tlaplusformatter.FormatConfig config) {
            super(config);
        }

        public Doc format(Doc prefix, List<String> extendedModules) {
            if (extendedModules.isEmpty()) {
                return Doc.empty();
            }
            ListFormatStrategy strategy = determineStrategy("EXTENDS", extendedModules.size());
            return formatList(extendedModules, prefix, stringFormatter(), strategy);
        }

        @Override
        protected ListFormatStrategy determineStrategy(String constructName, int itemCount) {
            if (itemCount <= 3) {
                return ListFormatStrategy.SINGLE_LINE;
            } else {
                return config.getConstructSetting(
                        constructName, "breakStrategy", ListFormatStrategy.SMART_BREAK);
            }
        }
    }
}