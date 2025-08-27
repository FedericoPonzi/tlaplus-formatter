package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

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
    public int getSupportedNodeKind() {
        return NodeKind.OPERATOR_DEFINITION.getId();
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
            System.out.println(config.getIndentSize());
            return Doc.group(
                    Doc.text(operatorName)
                            .append(Doc.text(" =="))
                            .appendLineOrSpace(expression)
            ).indent(config.getIndentSize());
        }
    }
}