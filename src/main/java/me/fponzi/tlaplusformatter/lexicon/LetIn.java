package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import me.fponzi.tlaplusformatter.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

import static me.fponzi.tlaplusformatter.TLAPlusFormatter.basePrintTree;

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
            basePrintTree(child, f);
            if (i < this.zero()[1].zero().length - 1
                    && !child.getImage().equals("N_Recursive") // RECURSIVE prints its own new line.
            ) {
                f.nl();
            }
        }
        f.decreaseIndent(4).nl();
        f.append(this.zero()[2]); // IN
        f.increaseIndent(4).nl();
        basePrintTree(this.zero()[3], f); // body
        f.decreaseIndent(4);
    }
}
