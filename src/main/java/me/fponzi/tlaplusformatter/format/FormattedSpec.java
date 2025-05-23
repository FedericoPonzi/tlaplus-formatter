package me.fponzi.tlaplusformatter.format;

import java.util.Stack;

public class FormattedSpec {
    public final StringBuffer out;
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

    public FormattedSpec append(String str) {
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

    public FormattedSpec nl() {
        out.append("\n");
        out.append(indent);
        return this;
    }

    /**
     * If the inner node is not too long,
     * we just add a space, otherwise we add a new line
     * and increase the level.
     * @param node
     * @return
     */
    public FormattedSpec nl(TreeNode node) {
        return nl(node, true);
    }

    public FormattedSpec nl(TreeNode node, boolean space) {
        if(node.shouldAddNewLine()){
            nl();
        } else {
            if(space) {
                space();
            }
        }
        return this;
    }

    public FormattedSpec space() {
        out.append(" ");
        return this;
    }

    public FormattedSpec append(TreeNode node) {
        for (String c: node.getPreComments()) {
            // Inline comments (that start with \n) include their new line character at the end.
            // TODO: they do not include all the subsequent \n - they are coalesced during parsing.
            // This means we will add all the new lines between this comment and the next statement before the comment itself.
            // check TreeNode#getPreCommentsRec.
            out.append(c.trim());
            this.nl();
        }
        out.append(node.getImage());
        return this;
    }

    private void setIndent(int val) {
        this.indent = " ".repeat(val);
    }
    public FormattedSpec increaseIndent(int val) {
        this.indent = " ".repeat(this.indent.length() + val);
        return this;
    }

    public FormattedSpec decreaseIndent(int val) {
        this.indent = " ".repeat(this.indent.length() - val);
        return this;
    }

}
