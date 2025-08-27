package me.fponzi.tlaplusformatter;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.ConstructRegistry;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import me.fponzi.tlaplusformatter.constructs.impl.*;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import tla2sany.st.TreeNode;

import java.lang.invoke.MethodHandles;
import java.util.ArrayList;
import java.util.List;

/**
 * New registry-based implementation of TlaDocBuilder.
 * Uses a plugin system for handling different TLA+ constructs.
 */
public class TlaDocBuilder {

    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    private final ConstructRegistry registry;
    private final ConstructContext context;
    private String originalSource;

    public TlaDocBuilder(FormatConfig config) {
        this.registry = new ConstructRegistry();
        this.context = new ConstructContext(config, this);
        registerDefaultConstructs();
    }

    /**
     * Register all default TLA+ constructs.
     */
    private void registerDefaultConstructs() {
        // Module structure
        registry.register(new ModuleConstruct.ModuleMainConstruct());
        registry.register(new ModuleConstruct.BeginModuleConstruct());
        registry.register(new ModuleConstruct.EndModuleConstruct());
        registry.register(new ModuleConstruct.BodyConstruct());

        // Declarations
        registry.register(new ExtendsConstruct());
        registry.register(new ConstantsConstruct());
        registry.register(new VariableConstruct());
        registry.register(new OperatorConstruct());

        // Basic elements
        registry.register(new BasicConstructs.IdentifierConstruct());
        registry.register(new BasicConstructs.NumberConstruct());
        registry.register(new BasicConstructs.TheoremConstruct());

        // Expressions
        registry.register(new IfThenElseConstruct());
    }

    /**
     * Main build method - now uses the registry system.
     */
    public Doc build(TreeNode node) {
        if (node == null) {
            return Doc.empty();
        }

        // Try to find a registered construct handler
        TlaConstruct construct = registry.findHandler(node);
        if (construct != null) {
            try {
                return construct.buildDoc(node, context);
            } catch (Exception e) {
                LOG.warn("Error building doc for construct {} on node kind {}: {}",
                        construct.getName(), node.getKind(), e.getMessage());
                // Fall back to generic handling
            }
        }

        // Fall back to generic handling
        return buildGeneric(node);
    }

    /**
     * Generic fallback handling for unknown node types.
     * This preserves the original behavior for unhandled nodes.
     */
    private Doc buildGeneric(TreeNode node) {
        String image = node.getImage();

        // Log unknown node types to help with future construct development
        if (image != null && image.startsWith("N_")) {
            LOG.debug("Generic node kind: {} image: '{}' hri: '{}'", node.getKind(), image, node.getHumanReadableImage());
        }

        if (image != null && !image.isEmpty() && !image.startsWith("N_")) {
            return Doc.text(image);
        }

        // If no meaningful image, try to build from children
        List<Doc> children = new ArrayList<>();

        if (node.zero() != null) {
            for (TreeNode child : node.zero()) {
                if (isValidNode(child)) {
                    Doc childDoc = build(child);
                    children.add(childDoc);
                }
            }
        }

        if (node.one() != null) {
            for (TreeNode child : node.one()) {
                if (isValidNode(child)) {
                    Doc childDoc = build(child);
                    children.add(childDoc);
                }
            }
        }

        if (children.isEmpty()) {
            return Doc.empty();
        }

        // Join children with spaces
        Doc result = children.get(0);
        for (int i = 1; i < children.size(); i++) {
            result = result.appendSpace(children.get(i));
        }

        return result;
    }

    /**
     * Checks if a node is valid (has a real location, not a placeholder).
     */
    private boolean isValidNode(TreeNode node) {
        if (node == null) {
            return false;
        }

        // SANY creates placeholder nodes with MAX_VALUE coordinates
        return node.getLocation() != null &&
                node.getLocation().beginLine() != Integer.MAX_VALUE;
    }

    /**
     * Allow external registration of new constructs.
     * This enables extensibility for future TLA+ constructs.
     */
    public void registerConstruct(TlaConstruct construct) {
        registry.register(construct);
    }

    /**
     * Get the construct registry (for inspection/debugging).
     */
    public ConstructRegistry getRegistry() {
        return registry;
    }

    /**
     * Get information about registered constructs.
     */
    public String getRegistryInfo() {
        StringBuilder info = new StringBuilder();
        info.append("Registered constructs (").append(registry.size()).append("):\n");

        for (TlaConstruct construct : registry.getAllConstructs()) {
            info.append("  ").append(construct.getName())
                    .append(" - handles node kinds: ").append(construct.getSupportedNodeKinds())
                    .append(" (priority: ").append(construct.getPriority()).append(")\n");
        }

        return info.toString();
    }

    /**
     * Set the original source content for spacing preservation.
     */
    public void setOriginalSource(String source) {
        this.originalSource = source;
    }

    /**
     * Get preserved spacing after a node based on original source.
     * Returns appropriate Doc for extra newlines between this node and the next.
     */
    public Doc getSpacingAfter(TreeNode node, TreeNode next) {
        if (originalSource == null || node == null || node.getLocation() == null) {
            return Doc.empty();
        }

        int nodeEndLine = node.getLocation().endLine(); // Convert to 0-based index
        int nextStartLine = next.getLocation().beginLine();
        if (nodeEndLine == Integer.MAX_VALUE || nextStartLine == Integer.MAX_VALUE) {
            return null;
        }
        // Count consecutive empty lines after this node (starting from the line after the node ends)
        int emptyLines = nextStartLine - nodeEndLine;
        // Return appropriate spacing (preserve extra newlines)
        if (emptyLines == 1) {
            return null;
        }
        Doc result = Doc.empty();
        for (int i = 1; i < emptyLines - 1; i++) {
            result = result.appendLine(Doc.empty());
        }
        System.out.println(emptyLines);
        return result;
    }
}