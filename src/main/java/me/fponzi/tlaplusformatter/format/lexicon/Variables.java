package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

public class Variables extends TreeNode {
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());
    public static final String IMAGE = "N_VariableDeclaration";
    public static final int KIND = 426;

    public Variables(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        var indent = this.zero()[0].getImage().length() + 1;
        f.append(this.zero()[0]); // VARIABLE
        f.increaseIndent(indent).nl();
        for (int i = 0; i < this.one().length; i++) {
            f.append(this.one()[i]);
            if (this.one()[i].getImage().equals(",") && i < this.one().length - 1) {
                f.nl();
            }
        }
        f.decreaseIndent(indent);
    }
}
