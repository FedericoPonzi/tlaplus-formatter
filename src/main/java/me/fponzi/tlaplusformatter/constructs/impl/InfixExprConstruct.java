package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import tla2sany.st.TreeNode;

import java.lang.invoke.MethodHandles;

/**
 * Construct implementation for infix expressions.
 * Handles formatting of expressions with infix operators (e.g., a + b, x :> y).
 */
public class InfixExprConstruct implements TlaConstruct {
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    @Override
    public String getName() {
        return "INFIX_EXPR";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.INFIX_EXPR.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        assert (node.zero() != null);
        assert (node.zero().length >= 3);
        // Expected structure:
        // zero[0]: left operand
        // zero[1]: infix operator
        // zero[2]: right operand
        // example: 1 .. 2

        Doc leftOperand = context.buildChild(node.zero()[0]);
        Doc operator = context.buildChild(node.zero()[1]);
        Doc rightOperand = context.buildChild(node.zero()[2]);

        return Doc.group(
                leftOperand
                        .appendSpace(operator)
                        .appendLineOrSpace(rightOperand)
        );
    }
}