package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

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
        this.zero()[0].format(f); // generalId.
        var o = this.one();
        f.append(o[0]); // [
        for (int i = 1; i < o.length - 1; i++) {
            if (i % 2 == 0) { // comma
                f.append(o[i]).space();
            } else {
                o[i].format(f);
            }
        }
        f.append(o[o.length - 1]); // ]
    }


}
