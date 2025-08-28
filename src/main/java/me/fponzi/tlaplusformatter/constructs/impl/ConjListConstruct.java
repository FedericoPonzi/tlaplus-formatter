package me.fponzi.tlaplusformatter.constructs.impl;

import me.fponzi.tlaplusformatter.constructs.NodeKind;

public class ConjListConstruct extends DisjListConstruct {
    @Override
    public String getName() {
        return "N_ConjList";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.CONJ_LIST.getId();
    }

}
