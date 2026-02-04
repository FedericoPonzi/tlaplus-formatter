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
 * Construct implementation for parenthesized expressions.
 * Handles formatting of expressions wrapped in parentheses.
 */
public class ParenExprConstruct implements TlaConstruct {
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    @Override
    public String getName() {
        return "PAREN_EXPR";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.PAREN_EXPR.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        assert (node.zero() != null && node.zero().length >= 3);
        Doc innerExpr = context.buildChild(node.zero()[1]);
        return Doc.group(context.buildChild(node.zero()[0]) // (
                .appendSpace(innerExpr.indent("( ".length()))
                .appendLineOrSpace(context.buildChild(node.zero()[node.zero().length - 1]))); // )
    }
}