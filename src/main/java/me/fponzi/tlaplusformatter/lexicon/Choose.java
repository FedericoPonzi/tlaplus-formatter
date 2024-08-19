package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import me.fponzi.tlaplusformatter.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

import static me.fponzi.tlaplusformatter.TLAPlusFormatter.basePrintTree;

// CHOOSE e \in S: TRUE
public class Choose extends TreeNode {
    public static final String IMAGE = "N_UnBoundedOrBoundedChoose";
    public static final int KIND = 424;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public Choose(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        var z = this.zero();
        f.append(z[0]).space(); // choose
        f.append(z[1]).space(); // var
        basePrintTree(z[2], f); // maybeBound
        f.append(z[3]); // :
        f.increaseLevel();
        f.space();
        basePrintTree(z[4], f); // condition
        f.decreaseLevel();
    }


}
