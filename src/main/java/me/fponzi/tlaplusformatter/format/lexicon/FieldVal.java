package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

/**
 * Has the form of: `[module, |->, "MCCRDT"]`
 */
public class FieldVal extends TreeNode {
    public static final String IMAGE = "FieldVal";
    public static final int KIND = 355;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public FieldVal(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        var z = this.zero();
        f.append(z[0]).space();
        z[1].format(f);
        f.increaseLevel();
        f.space();
        z[2].format(f);
        f.decreaseLevel();
    }
}
