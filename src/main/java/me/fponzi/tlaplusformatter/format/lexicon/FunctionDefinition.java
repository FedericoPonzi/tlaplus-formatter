package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

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
                o[i].format(f);
            }
        }
        f.append(o[o.length - 2]) // ==
                .increaseLevel()
                .space();
        o[o.length - 1].format(f); // Definition
        f.decreaseLevel();

    }

}
