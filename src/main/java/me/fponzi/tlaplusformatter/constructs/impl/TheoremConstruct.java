package me.fponzi.tlaplusformatter.constructs.impl;


import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Handles THEOREM declarations.
 */
public class TheoremConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "THEOREM";
    }

    @Override
    public int getSupportedNodeKind() {
        return -1;
        // TODO:
        //return NodeKind.THEOREM.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context) {
        if (node.one() != null && node.one().length > 0) {
            Doc expression = context.buildChild(node.one()[0]);
            return Doc.group(
                    Doc.text("THEOREM")
                            .appendLine(expression.indent(context.getConfig().getIndentSize()))
            );
        }

        return Doc.text("THEOREM");
    }
}