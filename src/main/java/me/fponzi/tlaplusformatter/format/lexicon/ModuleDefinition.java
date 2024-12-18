package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

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
        this.one()[0].format(f); // IdentLHS
        f.space().append(this.one()[1]); // ==
        f.increaseLevel().nl();
        this.one()[2].format(f); // N_NonLocalInstance.
        f.decreaseLevel();
    }

}
