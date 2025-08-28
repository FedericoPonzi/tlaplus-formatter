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
 * Example: `{Partitions(<<x>>\oseq,wt-x):x\inS}`
 * Example: RecordCombine(S, T) ==\n" +
 * "   {rc(s, t):s \\in S, t \\in T}
 */
public class SetOfAllConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_SetOfAll";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.SET_OF_ALL.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        List<Doc> zDoc = Arrays.stream(z).map(context::buildChild).collect(Collectors.toList());
        var ret = context.buildChild(z[0]);
        for (int i = 1; i < z.length; i++) {
            var b = context.buildChild(z[i]);
            if (z[i].getImage().equals(",") || z[i].getImage().equals(":")) {
                ret = ret.appendSpace(b);
            } else {
                ret = ret.appendLineOrSpace(b);
            }
        }
        return Doc.group(ret);
    }
}
