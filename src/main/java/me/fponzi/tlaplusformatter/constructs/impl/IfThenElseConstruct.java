package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Construct implementation for IF-THEN-ELSE expressions.
 */
public class IfThenElseConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "IF_THEN_ELSE";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.IF_THEN_ELSE.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        assert (node.zero() != null);
        assert (node.zero().length >= 6);
        // Expected structure:
        // zero[0]: IF keyword (kind=50)
        // zero[1]: condition expression  
        // zero[2]: THEN keyword (kind=62)
        // zero[3]: then expression
        // zero[4]: ELSE keyword (kind=45)
        // zero[5]: else expression
        Doc ifKey = context.buildChild(node.zero()[0]);
        Doc condition = Doc.group(context.buildChild(node.zero()[1]));
        Doc thenKey = context.buildChild(node.zero()[2]);
        Doc thenExpr = Doc.group(context.buildChild(node.zero()[3]));
        Doc elseKey = context.buildChild(node.zero()[4]);
        Doc elseExpr = Doc.group(context.buildChild(node.zero()[5]));
        return Doc.group(ifKey.appendSpace(condition))
                .appendLineOrSpace(thenKey.indent("IF".length())).appendSpace(thenExpr)
                .appendLineOrSpace(elseKey.indent("IF".length()).appendSpace(elseExpr));
    }
}