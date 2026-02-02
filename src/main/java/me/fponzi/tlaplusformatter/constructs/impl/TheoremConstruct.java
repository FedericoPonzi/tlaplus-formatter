package me.fponzi.tlaplusformatter.constructs.impl;


import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Handles THEOREM declarations.
 *
 * Unnamed theorem (THEOREM expr):
 *   zero[] = [THEOREM keyword, expression]
 *
 * Named theorem (THEOREM Name == expr):
 *   zero[] = [THEOREM keyword, name, ==, expression]
 */
public class TheoremConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "THEOREM";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.THEOREM.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length >= 2);

        var theoremKeyword = context.buildChild(z[0]);

        if (z.length == 2) {
            // Unnamed theorem: THEOREM expr
            var expr = context.buildChild(z[1]);
            return Doc.group(
                    theoremKeyword.appendLineOrSpace(expr)
            ).indent(z[0].getImage().length() + 1);
        } else {
            // Named theorem: THEOREM Name == expr
            assert z.length == 4;
            var name = context.buildChild(z[1]);
            var expr = context.buildChild(z[3]);
            return theoremKeyword
                    .appendSpace(name)
                    .appendSpace(Doc.text("=="))
                    .append(Doc
                            .group(Doc.lineOrSpace().append(expr))
                            .indent(indentSize));
        }
    }
}