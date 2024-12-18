package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

public class Tuple extends TreeNode {
    public static final String IMAGE = "N_Tuple";
    public static final int KIND = 423;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public Tuple(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        var z = this.zero();
        var len = z.length;
        f.append(z[0]); // <<
        f.increaseLevel().nl(this, false);
        for (int i = 1; i < len - 1; i++) {
            this.zero()[i].format(f);
            if (z[i + 1].getImage().equals(",")) {
                f.append(z[++i]);
                f.nl(this);
            }
        }
        f.decreaseLevel();
        f.nl(this, false);
        f.append(this.zero()[len - 1]);
    }
}
