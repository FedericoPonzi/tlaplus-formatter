package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public class DisjListConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_DisjList";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.DISJ_LIST.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length > 0);
        List<Doc> zDoc = Arrays.stream(z)
                .map(context::buildChild)
                .collect(Collectors.toList());
        Doc ret = Doc.line().append(zDoc.remove(0));
        for (Doc disL : zDoc) {
            ret = ret.appendLine(disL);
        }
        return Doc.group(ret);
    }
}
