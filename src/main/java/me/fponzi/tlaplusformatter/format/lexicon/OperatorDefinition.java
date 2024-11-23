package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

// S == 1 or S(x) == x + 1
// or a \odot b == c
// node.one()[0].zero()[0] is (usually) the identifier.
// node.one()[1] has the == sign.
public class OperatorDefinition extends TreeNode {
    public static final String IMAGE = "N_OperatorDefinition";
    public static final int KIND = 389;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public OperatorDefinition(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        var o = this.one();
        o[0].format(f);
        f.space().append(this.one()[1]); // ==
        f.increaseLevel().nl();
        this.one()[2].format(f);
        f.decreaseLevel();
    }
}
