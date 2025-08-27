package me.fponzi.tlaplusformatter.constructs;

import java.util.Arrays;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Enum representing SANY node kinds with metadata.
 */
public enum NodeKind {
    
    // Module structure
    MODULE(382, "Module declaration"),
    BEGIN_MODULE(333, "Module header"),
    END_MODULE(363, "Module footer"),
    BODY(336, "Module body", 334), // Multiple IDs for body
    
    // Declarations
    EXTENDS(365, "Extends declaration", 350), // Multiple IDs for extends
    CONSTANTS(392, "Constants declaration"),
    VARIABLE_DECLARATION(426, "Variable declaration"),
    OPERATOR_DEFINITION(389, "Operator definition"),
    THEOREM(421, "Theorem declaration"),
    
    // Basic elements
    IDENTIFIER(375, "Identifier"),
    NUMBER(387, "Number literal"),
    
    // Future extensibility - these can be added as constructs are implemented
    ASSUME(999, "Assume statement"), // Placeholder ID
    LEMMA(998, "Lemma declaration"), // Placeholder ID
    PROOF(997, "Proof block"), // Placeholder ID
    IF_THEN_ELSE(369, "IF-THEN-ELSE expression"), // N_IfThenElse
    FUNCTION_DEF(995, "Function definition"), // Placeholder ID
    SET_ENUM(994, "Set enumeration"), // Placeholder ID
    RECORD(993, "Record expression"), // Placeholder ID
    TUPLE(992, "Tuple expression"); // Placeholder ID
    
    private final int[] ids;
    private final String description;
    
    /**
     * Constructor for node kinds with a primary ID and optional alternate IDs.
     * 
     * @param primaryId The main SANY node kind ID
     * @param description Human-readable description
     * @param alternateIds Additional IDs that represent the same construct
     */
    NodeKind(int primaryId, String description, int... alternateIds) {
        this.ids = Stream.concat(
            Stream.of(primaryId), 
            Arrays.stream(alternateIds).boxed()
        ).mapToInt(Integer::intValue).toArray();
        this.description = description;
    }
    
    /**
     * Check if this NodeKind matches the given SANY node kind ID.
     * 
     * @param nodeKind The SANY node kind ID to check
     * @return true if this NodeKind handles the given ID
     */
    public boolean matches(int nodeKind) {
        return Arrays.stream(ids).anyMatch(id -> id == nodeKind);
    }
    
    /**
     * Get all node kind IDs handled by this NodeKind.
     * 
     * @return Set of all node kind IDs
     */
    public Set<Integer> getAllIds() {
        return Arrays.stream(ids).boxed().collect(Collectors.toSet());
    }
    
    /**
     * Get the primary (first) node kind ID.
     * 
     * @return The primary node kind ID
     */
    public int getPrimaryId() {
        return ids[0];
    }
    
    /**
     * Get the human-readable description.
     * 
     * @return Description of this node kind
     */
    public String getDescription() {
        return description;
    }
    
    /**
     * Find the NodeKind that matches the given SANY node kind ID.
     * 
     * @param nodeKind The SANY node kind ID
     * @return Optional containing the matching NodeKind, or empty if none found
     */
    public static Optional<NodeKind> fromNodeKind(int nodeKind) {
        return Arrays.stream(values())
                .filter(kind -> kind.matches(nodeKind))
                .findFirst();
    }
    
    /**
     * Get all node kind IDs for the given NodeKind values.
     * 
     * @param nodeKinds The NodeKind values
     * @return Set of all node kind IDs
     */
    public static Set<Integer> getAllIds(NodeKind... nodeKinds) {
        return Arrays.stream(nodeKinds)
                .flatMap(nk -> nk.getAllIds().stream())
                .collect(Collectors.toSet());
    }
    
    /**
     * Check if any of the given NodeKind values matches the node kind ID.
     * 
     * @param nodeKind The SANY node kind ID to check
     * @param candidates The NodeKind values to check against
     * @return true if any candidate matches
     */
    public static boolean anyMatches(int nodeKind, NodeKind... candidates) {
        return Arrays.stream(candidates).anyMatch(nk -> nk.matches(nodeKind));
    }
    
    @Override
    public String toString() {
        return String.format("%s(%s): %s", 
            name(), 
            Arrays.stream(ids).mapToObj(String::valueOf).collect(Collectors.joining(", ")),
            description);
    }
}