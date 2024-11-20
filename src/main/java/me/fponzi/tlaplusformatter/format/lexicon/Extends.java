package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;


public class Extends extends TreeNode {
    public static int KIND = 350;
    public static String IMAGE = "N_Extends";

    public Extends(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        if (this.zero() == null) {
            // no extends defined in this module.
            return;
        }
        f.append(this.zero()[0]) // EXTENDS
                .space();
        for (int i = 1; i < this.zero().length; i++) {
            f.append(this.zero()[i]);
            if (this.zero()[i].getImage().equals(",")) {
                f.space();
            }
        }
    }
}
