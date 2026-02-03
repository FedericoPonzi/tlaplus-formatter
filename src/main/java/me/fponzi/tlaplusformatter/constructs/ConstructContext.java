package me.fponzi.tlaplusformatter.constructs;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.FormatConfig;
import me.fponzi.tlaplusformatter.TlaDocBuilder;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import tla2sany.st.TreeNode;

import java.lang.invoke.MethodHandles;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Context object that provides access to shared services and utilities
 * for construct implementations.
 */
public class ConstructContext {

    private final FormatConfig config;
    private final TlaDocBuilder docBuilder;
    private final NodeAnalyzer nodeAnalyzer;

    public ConstructContext(FormatConfig config, TlaDocBuilder docBuilder) {
        this.config = config;
        this.docBuilder = docBuilder;
        this.nodeAnalyzer = new NodeAnalyzer();
    }

    /**
     * @return The current format configuration
     */
    public FormatConfig getConfig() {
        return config;
    }

    /**
     * Build a Doc for a child node using the main document builder.
     * This allows recursive building of nested constructs.
     *
     * @param child The child tree node
     * @return Doc object for the child node
     */
    public Doc buildChild(TreeNode child) {
        var childDoc = docBuilder.build(child);
        return addComments(child, childDoc);
    }

    public static Doc addComments(TreeNode node, Doc mainDoc) {
        String[] preComments = node.getPreComments();
        if (preComments == null || preComments.length == 0) {
            return mainDoc;
        }

        // Build comments, handling continuations properly.
        // SANY splits multi-line block comments at nested (* markers.
        // Continuation preComments (those not starting with (* or \*) should be
        // appended directly without adding a line break.
        Doc result = Doc.empty();
        boolean first = true;

        for (String comment : preComments) {
            boolean isContinuation = !isCommentStart(comment);
            String normalized = normalizeCommentWhitespace(comment, isContinuation);

            if (first) {
                result = Doc.text(normalized);
                first = false;
            } else if (isContinuation) {
                // Continuation: append directly without line break
                result = result.append(Doc.text(normalized));
            } else {
                // New comment: add line break first
                result = result.appendLine(Doc.text(normalized));
            }
        }

        // Add the main doc with a line break
        return result.appendLine(mainDoc);
    }

    /**
     * Check if a preComment string starts a new comment (vs being a continuation).
     * A new comment starts with (* (block) or \* (line).
     */
    private static boolean isCommentStart(String s) {
        // Skip leading whitespace to find the actual comment start
        int i = 0;
        while (i < s.length() && Character.isWhitespace(s.charAt(i))) {
            i++;
        }
        if (i >= s.length()) {
            return false;
        }
        // Check for block comment start (*
        if (i + 1 < s.length() && s.charAt(i) == '(' && s.charAt(i + 1) == '*') {
            return true;
        }
        // Check for line comment start \*
        if (i + 1 < s.length() && s.charAt(i) == '\\' && s.charAt(i + 1) == '*') {
            return true;
        }
        return false;
    }

    /**
     * Normalize comment whitespace.
     * For new comments (starting with (* or \*): strip leading whitespace and trailing newlines.
     * For continuations: only strip trailing newlines, preserve leading whitespace.
     * Always preserve trailing spaces before the newline (SANY's AST preserves them).
     */
    private static String normalizeCommentWhitespace(String s, boolean isContinuation) {
        int start = 0;
        // Only strip leading whitespace for new comments, not continuations
        if (!isContinuation) {
            while (start < s.length() && Character.isWhitespace(s.charAt(start))) {
                start++;
            }
        }
        // Strip trailing newlines only (preserve trailing spaces)
        int end = s.length();
        while (end > start && (s.charAt(end - 1) == '\n' || s.charAt(end - 1) == '\r')) {
            end--;
        }
        return s.substring(start, end);
    }

    /**
     * Extract string values from a tree node's children.
     * Common utility for constructs that work with lists of identifiers.
     *
     * @param node The parent tree node
     * @return List of non-empty string values from valid child nodes
     */
    public List<String> extractStringList(TreeNode node) {
        return nodeAnalyzer.extractStrings(node);
    }

    /**
     * Check if a tree node is valid (not a placeholder).
     *
     * @param node The tree node to check
     * @return true if the node is valid
     */
    public boolean isValidNode(TreeNode node) {
        return nodeAnalyzer.isValid(node);
    }

    /**
     * Get a construct-specific configuration setting.
     *
     * @param constructName Name of the construct
     * @param settingName   Name of the setting
     * @param defaultValue  Default value if setting is not found
     * @param <T>           Type of the setting value
     * @return The setting value or default value
     */
    public <T> T getConstructSetting(String constructName, String settingName, T defaultValue) {
        return config.getConstructSetting(constructName, settingName, defaultValue);
    }

    /**
     * Get preserved spacing after a node based on original source.
     *
     * @param node The tree node to get spacing after
     * @return Doc object for extra spacing/newlines
     */
    public Doc getSpacingAfter(TreeNode node, TreeNode next) {
        return docBuilder.getSpacingAfter(node, next);
    }

    /**
     * Helper class for common node analysis operations.
     */
    private static class NodeAnalyzer {
        private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

        /**
         * Check if a node is valid (has a real location, not a placeholder).
         */
        boolean isValid(TreeNode node) {
            if (node == null) {
                return false;
            }

            // SANY creates placeholder nodes with MAX_VALUE coordinates
            return node.getLocation() != null &&
                    node.getLocation().beginLine() != Integer.MAX_VALUE;
        }

        /**
         * Extract string values from a tree node, checking both zero() and one() arrays.
         */
        List<String> extractStrings(TreeNode node) {
            List<String> result = new ArrayList<>();

            // Check both zero() and one() arrays for child nodes
            TreeNode[] children = null;
            if (node.one() != null && node.one().length > 0) {
                children = node.one();
            } else if (node.zero() != null && node.zero().length > 0) {
                children = node.zero();
            }

            if (children != null) {
                for (TreeNode child : children) {
                    if (isValid(child) && child.getImage() != null) {
                        String image = child.getHumanReadableImage();
                        // Skip common separators and keywords
                        var toSkip = List.of(",", "EXTENDS", "VARIABLES", "VARIABLE", "CONSTANT", "CONSTANTS");
                        if (toSkip.contains(image)) {
                            continue;
                        }
                        result.add(image);
                    }
                }
            }

            return result;
        }
    }
}