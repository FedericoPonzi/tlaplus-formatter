package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.*;
import tla2sany.st.TreeNode;

import java.util.Set;

/**
 * Simple construct implementations for basic elements like identifiers, numbers, and theorems.
 */
public class BasicConstructs {
    
    /**
     * Handles identifier nodes.
     */
    public static class IdentifierConstruct implements TlaConstruct {
        
        @Override
        public String getName() {
            return "IDENTIFIER";
        }
        
        @Override
        public Set<Integer> getSupportedNodeKinds() {
            return NodeKind.IDENTIFIER.getAllIds();
        }
        
        @Override
        public Doc buildDoc(TreeNode node, ConstructContext context) {
            return Doc.text(node.getImage());
        }
    }
    
    /**
     * Handles number literal nodes.
     */
    public static class NumberConstruct implements TlaConstruct {
        
        @Override
        public String getName() {
            return "NUMBER";
        }
        
        @Override
        public Set<Integer> getSupportedNodeKinds() {
            return NodeKind.NUMBER.getAllIds();
        }
        
        @Override
        public Doc buildDoc(TreeNode node, ConstructContext context) {
            return Doc.text(node.getImage());
        }
    }
    
    /**
     * Handles THEOREM declarations.
     */
    public static class TheoremConstruct implements TlaConstruct {
        
        @Override
        public String getName() {
            return "THEOREM";
        }
        
        @Override
        public Set<Integer> getSupportedNodeKinds() {
            return NodeKind.THEOREM.getAllIds();
        }
        
        @Override
        public Doc buildDoc(TreeNode node, ConstructContext context) {
            if (node.one() != null && node.one().length > 0) {
                Doc expression = context.buildChild(node.one()[0]);
                return Doc.group(
                    Doc.text("THEOREM")
                        .appendLine(expression.indent(context.getConfig().getIndentSize()))
                );
            }
            return Doc.text("THEOREM");
        }
    }
}