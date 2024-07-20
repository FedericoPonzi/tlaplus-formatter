package me.fponzi.tlaplusformatter;

import tla2sany.st.TreeNode;

public class FormattedSpec {
    private final StringBuffer out;
    private String indent = "";

    public FormattedSpec() {
        out = new StringBuffer();
        indent = "";
    }

    public StringBuffer getOut() {
        return out;
    }

    protected FormattedSpec nl() {
        out.append("\n");
        out.append(indent);
        return this;
    }

    protected FormattedSpec space() {
        out.append(" ");
        return this;
    }

    protected FormattedSpec append(TreeNode node) {
        out.append(node.getImage());
        return this;
    }

    protected FormattedSpec appendSp(TreeNode node) {
        return this.append(node).space();
    }

    protected FormattedSpec increaseIndent(int val) {
        this.indent = " ".repeat(this.indent.length() + val);
        return this;
    }

    protected FormattedSpec decreaseIndent(int val) {
        this.indent = " ".repeat(this.indent.length() - val);
        return this;
    }
}
