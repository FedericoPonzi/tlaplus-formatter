package me.fponzi.tlaplusformatter;

import com.opencastsoftware.prettier4j.Doc;

import java.util.Arrays;
import java.util.List;

/**
 * Factory methods for creating Wadler Doc objects for common TLA+ constructs.
 * This class provides the building blocks for pretty-printing TLA+ specifications.
 */
public class TlaDocuments {
    
    private TlaDocuments() {
        // Utility class
    }
    
    /**
     * Creates a module header: ---- MODULE name ----
     */
    public static Doc moduleHeader(String moduleName) {
        String dashes = "----";
        return Doc.text(dashes)
                .append(Doc.text(" MODULE "))
                .append(Doc.text(moduleName))
                .append(Doc.text(" "))
                .append(Doc.text(dashes));
    }
    
    /**
     * Creates a module footer: ====
     */
    public static Doc moduleFooter() {
        return Doc.text("====");
    }
    
    /**
     * Creates a variable declaration: VARIABLE x, y, z or VARIABLES x, y, z
     */
    public static Doc variableDeclaration(List<String> variables) {
        if (variables.isEmpty()) {
            return Doc.empty();
        }
        
        String keyword = variables.size() == 1 ? "VARIABLE" : "VARIABLES";
        Doc header = Doc.text(keyword);
        
        if (variables.size() == 1) {
            return header.append(Doc.text(" ")).append(Doc.text(variables.get(0)));
        }
        
        // Multiple variables - create a group that can wrap
        Doc variableList = Doc.text(variables.get(0));
        for (int i = 1; i < variables.size(); i++) {
            variableList = variableList
                    .append(Doc.text(","))
                    .append(Doc.lineOrSpace())
                    .append(Doc.text(variables.get(i)));
        }
        
        return Doc.group(
            header
                .append(Doc.text(" "))
                .append(variableList)
        );
    }
    
    /**
     * Creates an operator definition: Op == expr
     * Uses line breaking: tries to fit on one line, falls back to indented new line
     */
    public static Doc operatorDefinition(String operatorName, Doc expression) {
        return Doc.group(
            Doc.text(operatorName)
                .append(Doc.text(" == "))
                .appendLineOrSpace(expression.indent(FormatConfig.DEFAULT_INDENT_SIZE))
        );
    }
    
    /**
     * Creates an EXTENDS declaration: EXTENDS Module1, Module2, ...
     * Uses smart line breaking for long module lists - tries to fit multiple modules
     * per line, then breaks to indented continuation lines when needed
     */
    public static Doc extendsDeclaration(List<String> modules) {
        if (modules.isEmpty()) {
            return Doc.empty();
        }
        
        if (modules.size() == 1) {
            return Doc.text("EXTENDS ").append(Doc.text(modules.get(0)));
        }
        
        // For short lists, keep simple formatting
        if (modules.size() <= 3) {
            Doc moduleList = Doc.text(modules.get(0));
            for (int i = 1; i < modules.size(); i++) {
                moduleList = moduleList.append(Doc.text(", ")).append(Doc.text(modules.get(i)));
            }
            return Doc.text("EXTENDS ").append(moduleList);
        }
        
        // For longer lists, use prettier4j line breaking  
        Doc moduleList = Doc.text(modules.get(0));
        for (int i = 1; i < modules.size(); i++) {
            moduleList = moduleList
                    .append(Doc.text(","))
                    .appendLineOrSpace(Doc.text(modules.get(i)));
        }
        
        // Use group to enable line breaking
        return Doc.group(
            Doc.text("EXTENDS ")
                .append(moduleList.indent("EXTENDS ".length()))
        );
    }
    
    /**
     * Creates an IF-THEN-ELSE expression
     */
    public static Doc ifThenElse(Doc condition, Doc thenExpr, Doc elseExpr) {
        return Doc.group(
            Doc.text("IF ")
                .append(condition)
                .appendLine(Doc.text("THEN"))
                .append(thenExpr.indent(FormatConfig.DEFAULT_INDENT_SIZE))
                .appendLine(Doc.text("ELSE"))
                .append(elseExpr.indent(FormatConfig.DEFAULT_INDENT_SIZE))
        );
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
    
    /**
     * Creates a theorem declaration: THEOREM expr
     */
    public static Doc theorem(Doc expression) {
        return Doc.group(
            Doc.text("THEOREM")
                .appendLine(expression.indent(FormatConfig.DEFAULT_INDENT_SIZE))
        );
    }
}