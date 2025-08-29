package me.fponzi.tlaplusformatter.constructs.impl;

import me.fponzi.tlaplusformatter.constructs.NodeKind;

public class IdentDeclConstruct extends AbstractAppendImageConstruct {

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.IDENT_DECL.getId();
    }

    @Override
    public String getName() {
        return "N_IdentDecl";
    }
}
