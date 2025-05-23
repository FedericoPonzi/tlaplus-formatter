package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

public class Theorem  extends TreeNode {
    public static final String IMAGE = "N_Theorem";
    public static final int KIND = 422;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public Theorem(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        var theoremKeyword = this.zero()[0];
        assert theoremKeyword.getImage().equals("THEOREM") && theoremKeyword.getKind() == 67;
        f.append(theoremKeyword).increaseLevel().nl();
        for (int i = 1; i < this.zero().length; i++) {
            this.zero()[i].format(f);
        }
        f.decreaseLevel();
    }
}
