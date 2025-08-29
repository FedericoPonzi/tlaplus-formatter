package me.fponzi.tlaplusformatter.constructs;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.FormatConfig;
import me.fponzi.tlaplusformatter.TlaDocBuilder;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import tla2sany.st.TreeNode;

import java.lang.invoke.MethodHandles;
import java.util.ArrayList;
import java.util.List;

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

        if (child.getPreComments().length > 0) {
            Doc comments = Doc.group(Doc.text(child.getPreComments()[0]));
            for (int z = 1; z < child.getPreComments().length; z++) {
                comments = comments.appendLine(Doc.group(Doc.text(child.getPreComments()[z]))).indent(0);
            }
            // TODO: if the comment is an inline comment and it's at the end of the line,
            //  we should leave it there
            return comments.appendLine(childDoc);
        }
        return childDoc;
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