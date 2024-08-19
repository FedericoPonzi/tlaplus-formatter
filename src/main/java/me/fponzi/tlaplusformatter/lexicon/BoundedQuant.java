package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import me.fponzi.tlaplusformatter.TreeNode;

import java.lang.invoke.MethodHandles;

import static me.fponzi.tlaplusformatter.TLAPlusFormatter.basePrintTree;

// \E coef \in [1..N -> -1..1] or \A QuantBound : ConjList.
public class BoundedQuant extends TreeNode {
    public static final String IMAGE = "N_BoundedQuant";
    public static final int KIND = 335;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public BoundedQuant(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        var z = this.zero();
        f.append(z[0]).space(); // \E
        for (int i = 1; i < z.length - 2; i++) {
            basePrintTree(z[i], f); // QuantBound
            if (i % 2 == 0) { // ,
                f.space();
            }
        }
        f.append(z[z.length - 2]); // :
        f.increaseLevel();
        f.space();
        basePrintTree(z[z.length - 1], f); // prop
        f.decreaseLevel();

    }


}
