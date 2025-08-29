package me.fponzi.tlaplusformatter;

import com.opencastsoftware.prettier4j.Doc;

import java.util.Arrays;
import java.util.List;

/**
 * Utility methods for creating common Doc patterns.
 * These are truly generic utilities not specific to TLA+ constructs.
 */
public class DocUtils {
    
    private DocUtils() {
        // Utility class
    }
    
    /**
     * Creates an infix expression: left op right
     */
    public static Doc infixExpression(Doc left, String operator, Doc right) {
        return Doc.group(
            left
                .append(Doc.text(" " + operator + " "))
                .append(right)
        );
    }
    
    /**
     * Creates a parenthesized expression: (expr)
     */
    public static Doc parentheses(Doc inner) {
        return Doc.text("(")
                .append(inner)
                .append(Doc.text(")"));
    }
    
    /**
     * Creates a sequence of documents separated by lines
     */
    public static Doc lines(Doc... docs) {
        return lines(Arrays.asList(docs));
    }
    
    /**
     * Creates a sequence of documents separated by lines
     */
    public static Doc lines(List<Doc> docs) {
        if (docs.isEmpty()) {
            return Doc.empty();
        }
        
        Doc result = docs.get(0);
        for (int i = 1; i < docs.size(); i++) {
            result = result.appendLine(docs.get(i));
        }
        return result;
    }
    
    /**
     * Creates a comment line starting with \*
     */
    public static Doc comment(String text) {
        return Doc.text("\\* " + text);
    }
}