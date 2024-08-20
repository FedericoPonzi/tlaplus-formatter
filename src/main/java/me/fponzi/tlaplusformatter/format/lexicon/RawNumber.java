package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

public class RawNumber extends TreeNode {
    public static final String IMAGE = "";
    public static final int KIND = 110;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public RawNumber(tla2sany.st.TreeNode node) {
        super(node);
    }
}
