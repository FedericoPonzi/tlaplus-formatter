package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 *
 * pc = [self \in ProcSet |-> CASE self = 0 -> "TM"
 * [] self \in ResourceManagers -> "RM"]
 */
public class FcnConstConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "FcnConst";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.FCN_CONST.getId();
    }

    /*
      /\ pc =
           [
             self \in ProcSet
             |->
             CASE self \in SlushQueryProcess -> "QueryReplyLoop"
             [] self \in SlushLoopProcess -> "RequireColorAssignment"
             [] self = "ClientRequest" -> "ClientRequestLoop"
           ]
     */

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length >= 4);
        // z[0] = [
        var qBound = context.buildChild(z[1]);
        var mapSymbol = context.buildChild(z[2]); // |->
        var mapExpr = context.buildChild(z[3]);
        // z[4] = ]
        return Doc.group(
                Doc.text("[")
                        .append(qBound)
                        .appendSpace(mapSymbol)
                        .appendLineOrSpace(mapExpr).indent(indentSize)
        ).appendLineOrEmpty(Doc.text("]"));
    }
}
