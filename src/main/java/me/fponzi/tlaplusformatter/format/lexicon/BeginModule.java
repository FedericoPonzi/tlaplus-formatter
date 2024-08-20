package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

public class BeginModule extends TreeNode {
    public static final String IMAGE = "N_BeginModule";
    public static final int KIND = 333;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public BeginModule(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        f.append(this.zero()[0]) // ---- MODULE
                .space()
                .append(this.zero()[1]) // name
                .space()
                .append(this.zero()[2]) // ----
                .nl()
                .nl();
    }
}
