package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

public class Assume extends TreeNode {
    public static final String IMAGE = "N_Assumption";
    public static final int KIND = 332;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public Assume(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        var one = this.one();

        f.append(one[0])
                .increaseLevel()
                .nl();
        one[1].format(f);
        // TODO: additional isolated test
        // I think this is a bug in SANY or something unexpected on the parsing output side.
        if (one.length > 3 && one[2].getImage().equals("==")) {
            //it's an op declaration.
            // one[1] has the id
            f.space();
            one[2].format(f); // ==
            f.increaseLevel();
            f.nl();
            one[3].format(f); // content
            f.decreaseLevel();
        }
        f.decreaseLevel();
    }
}
