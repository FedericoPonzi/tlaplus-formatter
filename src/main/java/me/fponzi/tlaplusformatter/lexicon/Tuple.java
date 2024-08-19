package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import me.fponzi.tlaplusformatter.TLAPlusFormatter;
import me.fponzi.tlaplusformatter.TreeNode;
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
        for (int i = 1; i < len - 1; i++) {
            TLAPlusFormatter.basePrintTree(this.zero()[i], f);
            if (i < this.zero().length - 2 && i % 2 == 0) {
                f.space(); // ,
            }
        }
        f.append(this.zero()[len - 1]); // >>
    }
}
