package me.fponzi.tlaplusformatter.format.lexicon;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import tla2sany.st.TreeNode;

import java.lang.invoke.MethodHandles;

public class DisjList extends ConjDisjList {
    public static final String IMAGE = "N_DisjList";
    public static final int KIND = 344;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public DisjList(TreeNode node) {
        super(node);
    }
}
