package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import me.fponzi.tlaplusformatter.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

import static me.fponzi.tlaplusformatter.TLAPlusFormatter.basePrintTree;

public class PostfixExpr extends TreeNode {
    public static final String IMAGE = "N_PostfixExpr";
    public static final int KIND = 395;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public PostfixExpr(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        basePrintTree(this.zero()[0], f);
        basePrintTree(this.zero()[1], f);
    }

}
