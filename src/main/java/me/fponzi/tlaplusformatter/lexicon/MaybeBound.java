package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import me.fponzi.tlaplusformatter.TreeNode;

import java.lang.invoke.MethodHandles;

import static me.fponzi.tlaplusformatter.TLAPlusFormatter.basePrintTree;

// Example: "\in S" from TowerOfHanoi test.
public class MaybeBound extends TreeNode {
    public static final String IMAGE = "N_MaybeBound";
    public static final int KIND = 381;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public MaybeBound(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        var z = this.zero();
        // Example: CHOOSE c : c \notin Color, it will create an empty MaybeBound
        if (z == null) return;
        f.append(z[0]).space();
        basePrintTree(z[1], f);
    }


}
