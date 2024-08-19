package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import me.fponzi.tlaplusformatter.TreeNode;

import java.lang.invoke.MethodHandles;

import static me.fponzi.tlaplusformatter.TLAPlusFormatter.basePrintTree;

//  pc = [self \in ProcSet |-> CASE self = 0 -> "TM"
//                               [] self \in ResourceManagers -> "RM"]
public class FcnConst extends TreeNode {
    public static final String IMAGE = "N_FcnConst";
    public static final int KIND = 353;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public FcnConst(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        var z = this.zero();
        f.append(z[0]); // [
        basePrintTree(z[1], f); // QuantBound
        f.append(z[2]); // |->
        f.increaseLevel();
        f.space();
        basePrintTree(z[3], f); // CASE or else
        f.append(z[4]); // ]
        f.decreaseLevel();
    }


}
