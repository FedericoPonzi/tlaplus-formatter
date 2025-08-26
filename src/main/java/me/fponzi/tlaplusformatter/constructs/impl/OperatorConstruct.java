package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.*;
import tla2sany.st.TreeNode;

import java.util.Set;

/**
 * Construct implementation for operator definitions.
 * Handles formatting of "Op == expr" constructs.
 */
public class OperatorConstruct implements TlaConstruct {
    
    @Override
    public String getName() {
        return "OPERATOR";
    }
    
    @Override
    public Set<Integer> getSupportedNodeKinds() {
        return NodeKind.OPERATOR_DEFINITION.getAllIds();
    }
    
    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context) {
        if (node.one() == null || node.one().length < 3) {
            // Fall back to generic handling if structure is unexpected
            return Doc.text(node.getImage() != null ? node.getImage() : "");
        }
        
        // node.one()[0] is the operator name/signature
        // node.one()[1] is the "==" 
        // node.one()[2] is the expression
        TreeNode nameNode = node.one()[0];
        TreeNode exprNode = node.one()[2];
        
        String operatorName = extractOperatorName(nameNode);
        Doc expression = context.buildChild(exprNode);
        
        return new OperatorFormatter(context.getConfig()).format(operatorName, expression);
    }
    
    private String extractOperatorName(TreeNode nameNode) {
        if (nameNode.zero() != null && nameNode.zero().length > 0) {
            return nameNode.zero()[0].getImage();
        }
        return nameNode.getImage();
    }
    
    /**
     * Dedicated formatter for operator definitions.
     */
    private static class OperatorFormatter {
        
        private final me.fponzi.tlaplusformatter.FormatConfig config;
        
        public OperatorFormatter(me.fponzi.tlaplusformatter.FormatConfig config) {
            this.config = config;
        }
        
        public Doc format(String operatorName, Doc expression) {
            return Doc.group(
                Doc.text(operatorName)
                    .append(Doc.text(" =="))
                    .appendLineOrSpace(expression.indent(config.getIndentSize()))
            );
        }
    }
}