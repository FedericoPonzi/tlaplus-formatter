package me.fponzi.tlaplusformatter;

/**
 * Configuration settings for the TLA+ formatter.
 * Contains formatting preferences like line width and indentation.
 */
public class FormatConfig {
    
    public static final int DEFAULT_LINE_WIDTH = 80;
    public static final int DEFAULT_INDENT_SIZE = 4;
    
    private final int lineWidth;
    private final int indentSize;
    
    public FormatConfig() {
        this(DEFAULT_LINE_WIDTH, DEFAULT_INDENT_SIZE);
    }
    
    public FormatConfig(int lineWidth, int indentSize) {
        if (lineWidth <= 0) {
            throw new IllegalArgumentException("Line width must be positive, got: " + lineWidth);
        }
        if (indentSize < 0) {
            throw new IllegalArgumentException("Indent size must be non-negative, got: " + indentSize);
        }
        
        this.lineWidth = lineWidth;
        this.indentSize = indentSize;
    }
    
    public int getLineWidth() {
        return lineWidth;
    }
    
    public int getIndentSize() {
        return indentSize;
    }
    
    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;
        
        FormatConfig that = (FormatConfig) obj;
        return lineWidth == that.lineWidth && indentSize == that.indentSize;
    }
    
    @Override
    public int hashCode() {
        return 31 * lineWidth + indentSize;
    }
    
    @Override
    public String toString() {
        return "FormatConfig{lineWidth=" + lineWidth + ", indentSize=" + indentSize + "}";
    }
}