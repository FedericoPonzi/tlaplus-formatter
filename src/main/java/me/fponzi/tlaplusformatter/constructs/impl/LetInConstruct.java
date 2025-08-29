package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public class LetInConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_LetIn";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.LET_IN.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length >= 4);
        List<Doc> zDoc = Arrays.stream(z).map(context::buildChild).collect(Collectors.toList());

        return Doc.group(
                zDoc.get(0)
                        .appendSpace(zDoc.get(1))
                        .appendLineOrSpace(zDoc.get(2).indent(indentSize))
                        .appendSpace(zDoc.get(3))
        );
    }
}
