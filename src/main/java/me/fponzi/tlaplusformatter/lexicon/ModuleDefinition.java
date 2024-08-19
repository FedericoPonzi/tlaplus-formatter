package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import me.fponzi.tlaplusformatter.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

import static me.fponzi.tlaplusformatter.TLAPlusFormatter.basePrintTree;

// Exmaple: N == INSTANCE B
// Example: N == INSTANCE Reachable WITH vroot<-vrootBar, pc<-pcBar TODO
public class ModuleDefinition extends TreeNode {
    public static final String IMAGE = "N_ModuleDefinition";
    public static final int KIND = 383;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public ModuleDefinition(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        basePrintTree(this.one()[0], f); // IdentLHS
        f.space().append(this.one()[1]); // ==
        f.increaseLevel().nl();
        basePrintTree(this.one()[2], f); // N_NonLocalInstance.
        f.decreaseLevel().nl().nl();
    }

}
