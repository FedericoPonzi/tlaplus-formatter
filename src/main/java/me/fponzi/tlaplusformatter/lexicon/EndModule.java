package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import me.fponzi.tlaplusformatter.TreeNode;

public class EndModule extends TreeNode {
    public static final String IMAGE = "N_EndModule";
    public static final int KIND = 345;

    public EndModule(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        f.append(this.zero()[0]).nl();
    }
}
