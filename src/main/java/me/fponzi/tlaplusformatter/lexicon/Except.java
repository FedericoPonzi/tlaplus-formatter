package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import me.fponzi.tlaplusformatter.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

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
        z[1].format(f); // generalId
        f.space().append(z[2]).space(); // EXCEPT
        int indentSpace = f.out.length() - lengthCheckpoint;
        f.increaseIndent(indentSpace);
        for (int i = 3; i < z.length - 1; i++) {
            z[i].format( f);
            if (i % 2 == 0) { // a comma
                f.nl();
            }
        }
        f.append(z[z.length - 1]); // ]
        f.decreaseIndent(indentSpace);
    }
}
