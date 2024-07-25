package me.fponzi.tlaplusformatter;

import tla2sany.st.TreeNode;

import java.util.Stack;

public class FormattedSpec {
    final StringBuffer out;
    String indent = "";
    Stack<Integer> indentLevels = new Stack<>();
    public FormattedSpec() {
        out = new StringBuffer();
        indent = "";
    }

    public int getLineLength() {
        // can be optimize because we keep track of \n
        return out.length() - out.lastIndexOf("\n");
    }

    protected FormattedSpec append(String str) {
        out.append(str);
        return this;
    }

    public FormattedSpec increaseLevel() {
        indentLevels.push(indent.length());
        setIndent(getLineLength());
        return this;
    }

    public FormattedSpec decreaseLevel() {
        setIndent(indentLevels.pop());
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
    protected FormattedSpec setIndent(int val) {
        this.indent = " ".repeat(val);
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
