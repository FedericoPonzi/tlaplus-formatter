package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Construct implementation for operator definitions.
 * Handles formatting of "Op == expr" constructs.
 * S == 1 or S(x) == x + 1
 * or a \odot b == c
 * node.one()[0].zero()[0] is (usually) the identifier.
 * node.one()[1] has the == sign.
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

        // node.one()[0] is the operator name/signature of type N_IdentLHS.
        // node.one()[1] is the "==" 
        // node.one()[2] is the expression
        var name = context.buildChild(node.one()[0]);
        var exprNode = context.buildChild(node.one()[2]);
        // todo: it's missing args.
        return Doc.group(
                name.appendSpace(
                                Doc.text("==")
                                        .appendLineOrSpace(exprNode))
                        .indent(indentSize)
        );
    }
}