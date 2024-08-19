package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import me.fponzi.tlaplusformatter.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

// x \in S
public class QuantBound extends TreeNode {
    public static final String IMAGE = "N_QuantBound";
    public static final int KIND = 408;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public QuantBound(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        var z = this.zero();
        var i = 0;
        // x1,x2,x3...
        while (!z[i].getImage().equals("\\in")) {
            f.append(z[i]);
            if (z[i].getImage().equals(",")) {
                f.space();
            }
            i++;
        }
        f.space().append(z[i]).space(); // \in
        i++;
        z[i].format(f); // S
    }


}
