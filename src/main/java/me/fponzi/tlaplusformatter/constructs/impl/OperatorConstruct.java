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
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        assert (node.one() != null && node.one().length >= 3);

        // node.one()[0] is the operator name/signature
        // node.one()[1] is the "==" 
        // node.one()[2] is the expression
        TreeNode nameNode = node.one()[0];
        TreeNode exprNode = node.one()[2];

        String operatorName = extractOperatorName(nameNode);
        Doc expression = context.buildChild(exprNode);
        return Doc.group(
                Doc.text(operatorName)
                        .appendSpace(Doc.text("=="))
                        .appendLineOrSpace(expression)
        ).indent(context.getConfig().getIndentSize());
    }

    private String extractOperatorName(TreeNode nameNode) {
        if (nameNode.zero() != null && nameNode.zero().length > 0) {
            return nameNode.zero()[0].getImage();
        }
        return nameNode.getImage();
    }
}