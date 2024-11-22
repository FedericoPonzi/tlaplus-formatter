package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

/**
 * Entry point for the format.
 * it represents a TLA+ Module.
 */
public class TlaModule extends TreeNode {
    public static final String IMAGE = "N_Module";
    public static final int KIND = 382;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public TlaModule(tla2sany.st.TreeNode node) {
        super(node);
    }
    @Override
    public void format(FormattedSpec f) {
        if(this.zero() == null) return;
        // Used to respect the newlines between different declartations
        // in the module's body.
        var lastRowPosition = getBeginLineSkipComments();
        for (var child : this.zero()) {
            if(child.getLocation().beginLine() == Integer.MAX_VALUE) {
                // Parsing of TlaModule will return a child also for elements that are missing.
                // For example, if a module doesn't extends anything, an EXTENDS will still be included.
                // So we just go ahead and skip it.
                continue;
            }
            var nextItemStart = child.getBeginLineSkipComments();
            while(nextItemStart > lastRowPosition) {
                f.nl();
                lastRowPosition++;
            }
            child.format(f);
            lastRowPosition = child.getLocation().endLine();
        }

    }
}
