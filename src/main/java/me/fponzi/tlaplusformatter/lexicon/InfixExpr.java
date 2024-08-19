package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import me.fponzi.tlaplusformatter.TreeNode;

import java.lang.invoke.MethodHandles;

import static me.fponzi.tlaplusformatter.TLAPlusFormatter.basePrintTree;

// Example: a \/ b
public class InfixExpr extends TreeNode {
    public static final String IMAGE = "N_InfixExpr";
    public static final int KIND = 371;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public InfixExpr(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        basePrintTree(this.zero()[0], f );
        f.space();
        basePrintTree(this.zero()[1], f);
        f.increaseLevel();
        f.space();
        basePrintTree(this.zero()[2], f);
        f.decreaseLevel();
    }


}
