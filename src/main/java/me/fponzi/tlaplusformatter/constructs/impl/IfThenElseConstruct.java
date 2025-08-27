package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
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
        assert (node.zero() != null);
        assert (node.zero().length >= 6);
        // Expected structure:
        // zero[0]: IF keyword (kind=50)
        // zero[1]: condition expression  
        // zero[2]: THEN keyword (kind=62)
        // zero[3]: then expression
        // zero[4]: ELSE keyword (kind=45)
        // zero[5]: else expression

        Doc condition = Doc.group(context.buildChild(node.zero()[1]));
        Doc thenExpr = Doc.group(context.buildChild(node.zero()[3]));
        Doc elseExpr = Doc.group(context.buildChild(node.zero()[5]));
        return create(condition, thenExpr, elseExpr, context.getConfig().getIndentSize());
    }

    /**
     * Utility method for creating IF-THEN-ELSE expressions.
     */
    public static Doc create(Doc condition, Doc thenExpr, Doc elseExpr, int indentSize) {
        return Doc.group(
                Doc.group(Doc.text("IF").appendLineOrSpace(condition))
                        .appendLineOrSpace(Doc.group(Doc.text("THEN").appendLineOrSpace(thenExpr)).indent(indentSize))
                        .appendLineOrSpace(Doc.group(Doc.text("ELSE").appendLineOrSpace(elseExpr)).indent(indentSize)).indent(indentSize)
        );
    }
}