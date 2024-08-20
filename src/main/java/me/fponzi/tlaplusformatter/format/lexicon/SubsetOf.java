package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

public class SubsetOf extends TreeNode {
    public static final String IMAGE = "N_SubsetOf";
    public static final int KIND = 419;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public SubsetOf(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        var z = this.zero();
        f.append(z[0]).space(); // {
        z[1].format(f); // x or a tuple like <<r, t>>
        f.space(); //
        f.append(z[2]).space(); // \in
        z[3].format(f); // S
        f.append(z[4]); // :
        f.increaseLevel();
        f.space();
        z[5].format(f);
        f.space().append(z[6]); // }
        f.decreaseLevel();
    }

}
