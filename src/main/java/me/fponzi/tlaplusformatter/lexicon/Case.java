package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import me.fponzi.tlaplusformatter.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

public class Case extends TreeNode {
    public static final String IMAGE = "N_Case";
    public static final int KIND = 336;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public Case(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        var z = this.zero();
        f.append(z[0]); // CASE
        f.space();
        f.increaseIndent(2);
        for (int i = 1; i < z.length; i++) {
            z[i].format(f);
            if (i % 2 == 1) {
                if (i < z.length - 1) {
                    f.nl();
                }
            } else {
                f.space();
            }

        }
        f.decreaseIndent(2);

    }


}
