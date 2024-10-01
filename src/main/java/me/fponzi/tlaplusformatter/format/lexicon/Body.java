package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

public class Body extends TreeNode {
    public static final String IMAGE = "N_Body";
    public static final int KIND = 334;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public Body(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        if (this.zero() == null) {
            // no body defined in this module.
            return;
        }
        for (var child : this.zero()) {
            child.format(f);
            if (child.getImage().equals("N_OperatorDefinition") && child.getKind() == 389) {
                f.nl().nl();
            } else if (child.getImage().equals("N_FunctionDefinition")) {
                f.nl();
            }
        }
    }

}