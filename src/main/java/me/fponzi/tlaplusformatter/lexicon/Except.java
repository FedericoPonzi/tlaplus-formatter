package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import me.fponzi.tlaplusformatter.TreeNode;

import java.lang.invoke.MethodHandles;

import static me.fponzi.tlaplusformatter.TLAPlusFormatter.basePrintTree;

public class Except extends TreeNode {
    public static final String IMAGE = "N_Except";
    public static final int KIND = 346;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public Except(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        int lengthCheckpoint = f.out.length();
        var z = this.zero();
        f.append(z[0]); // [
        basePrintTree(z[1], f); // generalId
        f.space().append(z[2]).space(); // EXCEPT
        int indentSpace = f.out.length() - lengthCheckpoint;
        f.increaseIndent(indentSpace);
        for (int i = 3; i < z.length - 1; i++) {
            basePrintTree(z[i], f);
            if (i % 2 == 0) { // a comma
                f.nl();
            }
        }
        f.append(z[z.length - 1]); // ]
        f.decreaseIndent(indentSpace);
    }
}
