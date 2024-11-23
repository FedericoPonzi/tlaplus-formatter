package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

public class ParamDeclaration extends TreeNode {
    public static final String IMAGE = "N_ParamDeclaration";
    public static final int KIND = 392;

    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public ParamDeclaration(tla2sany.st.TreeNode node) {
        super(node);
    }

    // Example: CONSTANTS A,B
    // Example: CONSTANT CalculateHash(_,_,_),
    @Override
    public void format(FormattedSpec f) {
        var constant = this.zero()[0].zero()[0];
        var indent = constant.getImage().length() + 1;
        f.append(constant).increaseIndent(indent).nl();

        // i=1 to skip CONSTANT[S] token
        for (int i = 1; i < this.zero().length; i++) {
            var child = this.zero()[i];
            if (child.getImage().equals(",")) {
                f.append(child).nl();
            } else {
                child.format(f);
            }
        }
        f.decreaseIndent(indent);
    }
}
