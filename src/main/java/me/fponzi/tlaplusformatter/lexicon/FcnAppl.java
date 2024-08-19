package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import me.fponzi.tlaplusformatter.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

import static me.fponzi.tlaplusformatter.TLAPlusFormatter.basePrintTree;

// Examples: towers[from] or CR[n - 1, v]
public class FcnAppl extends TreeNode {
    public static final String IMAGE = "N_FcnAppl";
    public static final int KIND = 352;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public FcnAppl(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        basePrintTree(this.zero()[0], f); // generalId.
        var o = this.one();
        f.append(o[0]); // [
        for (int i = 1; i < o.length - 1; i++) {
            if (i % 2 == 0) { // comma
                f.append(o[i]).space();
            } else {
                basePrintTree(o[i], f);
            }
        }
        f.append(o[o.length - 1]); // ]
    }


}
