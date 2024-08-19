package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import me.fponzi.tlaplusformatter.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

// Example: INSTANCE N WITH x<-a, y<-b
// Example: INSTANCE N
public class NonLocalInstance extends TreeNode {
    public static final String IMAGE = "N_NonLocalInstance";
    public static final int KIND = 376;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public NonLocalInstance(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        f.append(this.zero()[0]); // INSTANCE
        f.space();
        this.zero()[1].format(f); // module name
        if (this.zero().length == 2) {
            return;
        }
        f.space();
        f.append(this.zero()[2]); // WITH
        f.increaseLevel().space();
        // module parameters now, they are N_Substitution.
        for (int i = 3; i < this.zero().length; i++) {
            this.zero()[i].format(f);
            if (this.zero()[i].getImage().equals(",")) {
                f.nl();
            }
        }
        f.decreaseLevel();
    }

}
