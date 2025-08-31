package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.Arrays;
import java.util.stream.Collectors;

/**
 * Handles function definition constructs.
 * Example: `f[x \in S] == expr`
 * Example: `HostOf[pid \in SlushLoopProcess \cup SlushQueryProcess] == ...`
 */
public class FunctionDefinitionConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_FunctionDefinition";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.FUNCTION_DEFINITION.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var o = node.one();
        assert (o != null && o.length == 6);
        var oDoc = Arrays.stream(o).map(context::buildChild).collect(Collectors.toList());
        return Doc.group(
                oDoc.get(0) // function name
                        .append(oDoc.get(1))// [
                        .append(oDoc.get(2)) // bound variables
                        .append(oDoc.get(3)) // ]
                        .appendSpace(oDoc.get(4)) // ==
                        .appendLineOrSpace(oDoc.get(5)) // expr
        ).indent(indentSize);
    }
}
