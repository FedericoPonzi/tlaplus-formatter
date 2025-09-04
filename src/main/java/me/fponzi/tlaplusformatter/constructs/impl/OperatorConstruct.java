package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Construct implementation for operator definitions.
 * Handles formatting of "Op == expr" constructs.
 * N_IdentLHS == expr
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
        var o = node.one();
        assert (o != null && o.length >= 3);
        // QueryReplyLoop
        var name = context.buildChild(o[0]);
        var exprNode = context.buildChild(o[2]);
        return name
                .appendSpace(Doc.text("=="))
                .append(Doc
                        .group(Doc.lineOrSpace().append(exprNode))
                        .indent(indentSize));
    }
}