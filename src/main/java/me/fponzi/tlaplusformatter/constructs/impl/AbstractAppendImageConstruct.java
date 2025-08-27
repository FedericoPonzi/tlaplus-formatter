package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

public abstract class AbstractAppendImageConstruct implements TlaConstruct {
    public abstract int getSupportedNodeKind();

    public abstract String getName();

    @Override
    public final Doc buildDoc(TreeNode node, ConstructContext context) {
        return Doc.text(node.getHumanReadableImage());
    }
}
