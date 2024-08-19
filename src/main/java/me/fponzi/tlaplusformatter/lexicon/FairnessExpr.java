package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import me.fponzi.tlaplusformatter.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

import static me.fponzi.tlaplusformatter.TLAPlusFormatter.basePrintTree;

// Example:
// WF_vars(\E i, j \in Proc: IF i # root /\ prnt[i] = NoPrnt /\ <<j, i>> \in msg
//                                     THEN Update(i, j)
//                                     ELSE \/ Send(i) \/ Parent(i)
//                                          \/ UNCHANGED <<prnt, msg, rpt>>)
public class FairnessExpr extends TreeNode {
    public static final String IMAGE = "";
    public static final int KIND = 351;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public FairnessExpr(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        var lengthCheckPoint = f.out.length();
        var z = this.zero();
        f.append(z[0]); // WF_
        basePrintTree(z[1], f); // vars
        f.append(z[2]); // (
        var indentSpace = f.out.length() - lengthCheckPoint;
        f.increaseIndent(indentSpace);
        basePrintTree(z[3], f); // expr
        f.decreaseIndent(indentSpace)
                .append(z[4]); // )
    }


}
