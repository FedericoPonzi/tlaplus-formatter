package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import me.fponzi.tlaplusformatter.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

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
        this.zero()[0].format(f );
        f.space();
        this.zero()[1].format(f);
        f.increaseLevel();
        f.space();
        this.zero()[2].format(f);
        f.decreaseLevel();
    }


}
