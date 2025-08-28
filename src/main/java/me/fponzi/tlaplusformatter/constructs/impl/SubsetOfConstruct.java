package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Example: {x\in1..max:/\(r-1)=<(wt-x)/\wt=<x*r}
 */
public class SubsetOfConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "N_SubsetOf";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.SUBSET_OF.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        List<Doc> zDoc = Arrays.stream(z).map(context::buildChild).collect(Collectors.toList());
        return Doc.group(
                zDoc.get(0) // {
                        .append(zDoc.get(1)) // x or a tuple like <<r,t>>
                        .appendLineOrSpace(zDoc.get(2)) //\in
                        .appendSpace(zDoc.get(3)) // S
                        .append(zDoc.get(4)) // :
                        .appendLineOrSpace(zDoc.get(5))
                        .appendSpace(zDoc.get(6))
        );
    }
}
