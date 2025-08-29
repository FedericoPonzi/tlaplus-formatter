package me.fponzi.tlaplusformatter.constructs.impl;

import me.fponzi.tlaplusformatter.constructs.NodeKind;

public class GenPostfixOpConstruct extends AbstractAppendImageConstruct {
    @Override
    public int getSupportedNodeKind() {
        return NodeKind.GEN_POSTFIX_OP.getId();
    }

    @Override
    public String getName() {
        return "N_GenPostfixOp";
    }
}
