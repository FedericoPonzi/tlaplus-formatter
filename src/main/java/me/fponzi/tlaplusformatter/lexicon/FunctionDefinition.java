package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import me.fponzi.tlaplusformatter.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

import static me.fponzi.tlaplusformatter.TLAPlusFormatter.basePrintTree;

// Example:
// CR[n \in Nat ,v \in S ]==IF n = 0 THEN R(s, v) ELSE
//   \/ CR[n - 1,
//   \/ \E u \in S : CR[n - 1, /\ R(u, v)
public class FunctionDefinition extends TreeNode {
    public static final String IMAGE = "N_FunctionDefinition";
    public static final int KIND = 356;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public FunctionDefinition(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        var o = this.one();
        f.append(o[0]); // function name
        f.append(o[1]); // [
        for (int i = 2; i < o.length - 2; i++) {
            if (i % 2 == 1) { // comma
                f.append(o[i]).space();
            } else {
                basePrintTree(o[i], f);
            }
        }
        f.append(o[o.length - 2]) // ==
                .increaseLevel()
                .space();
        basePrintTree(o[o.length - 1], f); // Definition
        f.decreaseLevel();

    }

}
