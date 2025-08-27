package me.fponzi.tlaplusformatter.constructs;

import tla2sany.st.TreeNode;

import java.util.*;
import java.util.concurrent.ConcurrentHashMap;

/**
 * Registry for managing TLA+ construct handlers.
 * Provides efficient lookup of construct handlers by node kind.
 */
public class ConstructRegistry {

    private final Map<Integer, List<TlaConstruct>> handlersByNodeKind;
    private final Set<TlaConstruct> allHandlers;

    public ConstructRegistry() {
        this.handlersByNodeKind = new ConcurrentHashMap<>();
        this.allHandlers = new LinkedHashSet<>();
    }

    /**
     * Register a construct handler.
     *
     * @param construct The construct to register
     */
    public void register(TlaConstruct construct) {
        if (construct == null) {
            throw new IllegalArgumentException("Construct cannot be null");
        }

        synchronized (this) {
            // Add to global set
            allHandlers.add(construct);

            // Add to per-node-kind maps for efficient lookup
            for (Integer nodeKind : construct.getSupportedNodeKinds()) {
                handlersByNodeKind.computeIfAbsent(nodeKind, k -> new ArrayList<>())
                        .add(construct);

                // Sort by priority (higher priority first)
                handlersByNodeKind.get(nodeKind);
            }
        }
    }

    /**
     * Find a construct handler for the given tree node.
     *
     * @param node The tree node to find a handler for
     * @return The best matching construct handler, or null if none found
     */
    public TlaConstruct findHandler(TreeNode node) {
        if (node == null) {
            return null;
        }

        List<TlaConstruct> candidates = handlersByNodeKind.get(node.getKind());
        if (candidates == null || candidates.isEmpty()) {
            return null;
        }

        // Return the first handler that can handle this node
        // (candidates are already sorted by priority)
        for (TlaConstruct construct : candidates) {
            if (construct.canHandle(node)) {
                return construct;
            }
        }

        return null;
    }

    /**
     * Get all registered constructs.
     *
     * @return Unmodifiable set of all registered constructs
     */
    public Set<TlaConstruct> getAllConstructs() {
        return Collections.unmodifiableSet(allHandlers);
    }

    /**
     * Get all constructs that handle the specified node kind.
     *
     * @param nodeKind The SANY node kind
     * @return List of constructs that can handle this node kind (sorted by priority)
     */
    public List<TlaConstruct> getHandlersForNodeKind(int nodeKind) {
        List<TlaConstruct> handlers = handlersByNodeKind.get(nodeKind);
        return handlers != null ? Collections.unmodifiableList(handlers) : Collections.emptyList();
    }

    /**
     * Check if any construct is registered for the given node kind.
     *
     * @param nodeKind The SANY node kind
     * @return true if at least one construct can handle this node kind
     */
    public boolean hasHandlerFor(int nodeKind) {
        List<TlaConstruct> handlers = handlersByNodeKind.get(nodeKind);
        return handlers != null && !handlers.isEmpty();
    }

    /**
     * Remove a construct from the registry.
     *
     * @param construct The construct to remove
     * @return true if the construct was removed, false if it wasn't registered
     */
    public boolean unregister(TlaConstruct construct) {
        if (construct == null) {
            return false;
        }

        synchronized (this) {
            boolean removed = allHandlers.remove(construct);
            if (removed) {
                // Remove from node kind maps
                for (Integer nodeKind : construct.getSupportedNodeKinds()) {
                    List<TlaConstruct> handlers = handlersByNodeKind.get(nodeKind);
                    if (handlers != null) {
                        handlers.remove(construct);
                        if (handlers.isEmpty()) {
                            handlersByNodeKind.remove(nodeKind);
                        }
                    }
                }
            }
            return removed;
        }
    }

    /**
     * Clear all registered constructs.
     */
    public void clear() {
        synchronized (this) {
            allHandlers.clear();
            handlersByNodeKind.clear();
        }
    }

    /**
     * Get the number of registered constructs.
     *
     * @return Number of registered constructs
     */
    public int size() {
        return allHandlers.size();
    }
}