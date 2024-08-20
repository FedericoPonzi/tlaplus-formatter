package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

public class Number extends TreeNode {
    public static final String IMAGE = "N_Number";
    public static final int KIND = 385;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public Number(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        // it has a (RawNumber) number in the zero()[0] position.
        if (this.zero() != null) {
            for (var child : this.zero()) {
                child.format(f);
            }
        }
    }


}
