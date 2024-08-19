package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import me.fponzi.tlaplusformatter.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

// Example:
// CONSTANT CalculateHash(_,_,_)
public class IdentDecl extends TreeNode {
    public static final String IMAGE = "N_IdentDecl";
    public static final int KIND = 363;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public IdentDecl(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        var z = this.zero();
        for (var ch : z) {
            f.append(ch);
        }
    }

}
