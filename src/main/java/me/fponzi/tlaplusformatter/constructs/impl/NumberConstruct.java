package me.fponzi.tlaplusformatter.constructs.impl;

import me.fponzi.tlaplusformatter.constructs.NodeKind;

/**
 * Handles number literal nodes.
 */
public class NumberConstruct extends AbstractAppendImageConstruct {

    @Override
    public String getName() {
        return "NUMBER";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.NUMBER.getId();
    }
}