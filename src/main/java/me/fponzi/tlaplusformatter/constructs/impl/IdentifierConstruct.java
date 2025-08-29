package me.fponzi.tlaplusformatter.constructs.impl;

import me.fponzi.tlaplusformatter.constructs.NodeKind;

public class IdentifierConstruct extends AbstractAppendImageConstruct {

    @Override
    public String getName() {
        return "IDENTIFIER";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.GENERAL_ID.getId();
    }
}