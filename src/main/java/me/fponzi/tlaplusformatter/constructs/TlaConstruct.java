package me.fponzi.tlaplusformatter.constructs;

import com.opencastsoftware.prettier4j.Doc;
import tla2sany.st.TreeNode;

/**
 * Interface for all TLA+ language constructs that can be formatted.
 * This provides a plugin-like system for handling different TLA+ syntax elements.
 */
public interface TlaConstruct {

    /**
     * @return The name of this construct (e.g., "EXTENDS", "VARIABLES", "OPERATOR")
     */
    String getName();

    /**
     * @return SANY node kind that this construct can handle
     */
    int getSupportedNodeKind();

    /**
     * Check if this construct can handle the given node.
     * Default implementation checks if the node kind is in getSupportedNodeKinds().
     *
     * @param node The tree node to check
     * @return true if this construct can handle the node
     */
    default boolean canHandle(TreeNode node) {
        return node != null && getSupportedNodeKind() == node.getKind();
    }

    /**
     * Build a Doc object for formatting this construct.
     *
     * @param node       The SANY tree node representing this construct
     * @param context    Context object providing access to configuration and utilities
     * @param indentSize
     * @return A Doc object for pretty printing
     */
    Doc buildDoc(TreeNode node, ConstructContext context, int indentSize);

    /**
     * Default indent size, pulled from the formatter configuration.
     *
     * @param context Construct context providing access to config
     * @return indent size from config
     */
    default int indentSize(ConstructContext context) {
        return context.getConfig().getIndentSize();
    }
}