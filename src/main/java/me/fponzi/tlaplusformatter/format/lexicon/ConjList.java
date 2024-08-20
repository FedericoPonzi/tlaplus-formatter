package me.fponzi.tlaplusformatter.format.lexicon;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import tla2sany.st.TreeNode;

import java.lang.invoke.MethodHandles;

public class ConjList extends ConjDisjList {
    public static final String IMAGE = "N_ConjList";
    public static final int KIND = 341;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public ConjList(TreeNode node) {
        super(node);
    }
}
