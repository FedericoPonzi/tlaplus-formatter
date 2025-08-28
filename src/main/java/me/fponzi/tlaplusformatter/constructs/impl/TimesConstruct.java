package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

public class TimesConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "N_Times";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.TIMES.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null);
        assert (z.length >= 3);
        // Expected structure:
        // zero[0]: A
        // zero[1]: \X
        // zero[2]: B
        // example: A \X B

        Doc leftOperand = context.buildChild(z[0]);
        Doc operator = context.buildChild(z[1]);
        Doc rightOperand = context.buildChild(z[2]);

        return Doc.group(
                leftOperand
                        .appendSpace(operator)
                        .appendLineOrSpace(rightOperand).indent(indentSize)
        );
    }
}
