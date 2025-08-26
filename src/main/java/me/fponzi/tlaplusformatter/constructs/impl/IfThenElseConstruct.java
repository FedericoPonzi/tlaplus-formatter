package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.*;
import tla2sany.st.TreeNode;

import java.util.Set;

/**
 * Construct implementation for IF-THEN-ELSE expressions.
 */
public class IfThenElseConstruct implements TlaConstruct {
    
    @Override
    public String getName() {
        return "IF_THEN_ELSE";
    }
    
    @Override
    public Set<Integer> getSupportedNodeKinds() {
        return NodeKind.IF_THEN_ELSE.getAllIds();
    }
    
    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context) {
        // This would need to be implemented based on SANY's parse tree structure
        // For now, provide a utility method for manual construction
        return Doc.text("IF"); // Placeholder
    }
    
    /**
     * Utility method for creating IF-THEN-ELSE expressions.
     */
    public static Doc create(Doc condition, Doc thenExpr, Doc elseExpr, int indentSize) {
        return Doc.group(
            Doc.text("IF ")
                .append(condition)
                .appendLine(Doc.text("THEN"))
                .append(thenExpr.indent(indentSize))
                .appendLine(Doc.text("ELSE"))
                .append(elseExpr.indent(indentSize))
        );
    }
}