package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

public class LetIn extends TreeNode {
    public static final String IMAGE = "N_LetIn";
    public static final int KIND = 380;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public LetIn(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        f.append(this.zero()[0]).
                increaseIndent(4).nl(); // LET
        for (int i = 0; i < this.zero()[1].zero().length; i++) {
            var child = this.zero()[1].zero()[i];
            child.format(f);
            if (i < this.zero()[1].zero().length - 1) {
                f.nl();
            }
        }
        f.decreaseIndent(4).nl();
        f.append(this.zero()[2]); // IN
        f.increaseIndent(4).nl();
        this.zero()[3].format(f); // body
        f.decreaseIndent(4);
    }
}
