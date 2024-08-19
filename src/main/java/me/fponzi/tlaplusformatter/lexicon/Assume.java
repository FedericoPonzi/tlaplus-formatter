package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import me.fponzi.tlaplusformatter.TLAPlusFormatter;
import me.fponzi.tlaplusformatter.TreeNode;
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
        LOG.debug("Found ASSUME");
        var one = this.one();

        f.append(one[0])
                .increaseLevel()
                .nl();
        TLAPlusFormatter.basePrintTree(one[1], f);
        // TODO: additional isolated test
        // I think this is a bug in SANY or something unexpected on the parsing output side.
        if (one.length > 3 && one[2].getImage().equals("==")) {
            //it's an op declaration.
            // one[1] has the id
            f.space();
            TLAPlusFormatter.basePrintTree(one[2], f); // ==
            f.increaseLevel();
            f.nl();
            TLAPlusFormatter.basePrintTree(one[3], f); // content
            f.decreaseLevel();
        }
        f.decreaseLevel()
                .nl()
                .nl();
    }
}
