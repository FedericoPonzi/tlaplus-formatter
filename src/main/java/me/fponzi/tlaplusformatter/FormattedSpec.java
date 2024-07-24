package me.fponzi.tlaplusformatter;

import tla2sany.st.TreeNode;

public class FormattedSpec {
    final StringBuffer out;
    String indent = "";

    public FormattedSpec() {
        out = new StringBuffer();
        indent = "";
    }
    protected FormattedSpec append(String str) {
        out.append(str);
        return this;
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
        for (String c: node.getPreComments()) {
            // Inline comments (that start with \n) include their new line character at the end.
            out.append(c.trim());
            this.nl();
        }
        out.append(node.getImage());
        return this;
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
