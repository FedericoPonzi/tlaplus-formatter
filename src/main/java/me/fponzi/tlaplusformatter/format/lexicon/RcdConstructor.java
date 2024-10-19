package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

/**
 * Example: [ action |-> {} ]
 * it's '[', N_FieldVal, ']'.
 */
public class RcdConstructor extends TreeNode {
    public static final String IMAGE = "RcdConstructor";
    public static final int KIND = 409;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public RcdConstructor(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        var z = this.zero();
        z[0].format(f);
        f.increaseLevel();
        f.nl();
        for (int i = 1; i < z.length - 1; i++) {
            z[i].format(f);
            if (z[i + 1].getImage().equals(",")) {
                f.append(z[++i]).nl();
            }
        }
        f.decreaseLevel();
        f.nl();
        z[z.length - 1].format(f);
    }
}
