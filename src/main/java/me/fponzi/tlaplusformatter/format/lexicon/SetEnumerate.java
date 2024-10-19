package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

public class SetEnumerate extends TreeNode {
    public static final String IMAGE = "SetEnumerate";
    public static final int KIND = 411;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public SetEnumerate(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        var z = this.zero();
        z[0].format(f); // {
        f.increaseLevel().nl();
        for (int i = 1; i < z.length - 1; i++) {
            z[i].format(f);
            if (z[i + 1].getImage().equals(",")) {
                z[++i].format(f);
                f.nl();
            }
        }
        f.decreaseLevel();
        f.nl();
        z[z.length - 1].format(f);
    }

}
