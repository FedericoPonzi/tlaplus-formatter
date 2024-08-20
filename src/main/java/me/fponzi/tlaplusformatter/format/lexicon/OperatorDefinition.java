package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;
import java.util.List;
import java.util.Objects;

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
        for (int i = 0; i < o[0].zero().length; i++) {
            var ch = this.one()[0].zero()[i];
            ch.format(f);
            if (i + 1 < o[0].zero().length && !(List.of(",", "(", ")").contains(o[0].zero()[i + 1].getImage())) && !Objects.equals("(", ch.getImage())) {
                f.space();
            } else if (ch.getImage().equals(",")) f.space();
        }
        f.space().append(this.one()[1]); // ==
        f.increaseLevel().nl();
        this.one()[2].format(f);
        f.decreaseLevel();
    }
}
