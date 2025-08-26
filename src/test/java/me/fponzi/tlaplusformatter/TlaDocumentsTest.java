package me.fponzi.tlaplusformatter;

import com.opencastsoftware.prettier4j.Doc;
import org.junit.jupiter.api.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for TlaDocuments factory methods.
 */
class TlaDocumentsTest {

    @Test
    void testModuleHeader() {
        Doc header = TlaDocuments.moduleHeader("TestModule");
        String result = header.render(80);
        
        assertEquals("---- MODULE TestModule ----", result);
    }

    @Test
    void testModuleFooter() {
        Doc footer = TlaDocuments.moduleFooter();
        String result = footer.render(80);
        
        assertEquals("====", result);
    }

    @Test
    void testSingleVariableDeclaration() {
        List<String> variables = Collections.singletonList("x");
        Doc varDecl = TlaDocuments.variableDeclaration(variables);
        String result = varDecl.render(80);
        
        assertEquals("VARIABLE x", result);
    }

    @Test
    void testMultipleVariableDeclaration() {
        List<String> variables = Arrays.asList("x", "y", "z");
        Doc varDecl = TlaDocuments.variableDeclaration(variables);
        String result = varDecl.render(80);
        
        assertTrue(result.startsWith("VARIABLES"));
        assertTrue(result.contains("x"));
        assertTrue(result.contains("y"));
        assertTrue(result.contains("z"));
    }

    @Test
    void testEmptyVariableDeclaration() {
        List<String> variables = Collections.emptyList();
        Doc varDecl = TlaDocuments.variableDeclaration(variables);
        String result = varDecl.render(80);
        
        assertEquals("", result);
    }

    @Test
    void testOperatorDefinition() {
        Doc expr = Doc.text("x + 1");
        Doc opDef = TlaDocuments.operatorDefinition("Inc", expr);
        String result = opDef.render(80);
        
        assertTrue(result.contains("Inc =="));
        assertTrue(result.contains("x + 1"));
    }

    @Test
    void testExtendsDeclaration() {
        List<String> modules = Arrays.asList("Naturals", "TLC", "TLC", "TLC", "TLC","TLC","TLC","TLC");
        Doc extends_ = TlaDocuments.extendsDeclaration(modules);
        String result = extends_.render(80);
        assertEquals("EXTENDS Naturals, TLC, TLC, TLC, TLC, TLC, TLC, TLC", result);
        result = extends_.render(20);
        assertEquals("EXTENDS Naturals,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC,\n" +
                "        TLC", result);

    }

    @Test
    void testSingleExtendsDeclaration() {
        List<String> modules = Collections.singletonList("Naturals");
        Doc extends_ = TlaDocuments.extendsDeclaration(modules);
        String result = extends_.render(80);
        
        assertEquals("EXTENDS Naturals", result);
    }

    @Test
    void testEmptyExtendsDeclaration() {
        List<String> modules = Collections.emptyList();
        Doc extends_ = TlaDocuments.extendsDeclaration(modules);
        String result = extends_.render(80);
        
        assertEquals("", result);
    }

    @Test
    void testIfThenElse() {
        Doc condition = Doc.text("x > 0");
        Doc thenExpr = Doc.text("x + 1");
        Doc elseExpr = Doc.text("0");
        
        Doc ifThenElse = TlaDocuments.ifThenElse(condition, thenExpr, elseExpr);
        String result = ifThenElse.render(80);
        
        assertTrue(result.contains("IF"));
        assertTrue(result.contains("x > 0"));
        assertTrue(result.contains("THEN"));
        assertTrue(result.contains("x + 1"));
        assertTrue(result.contains("ELSE"));
        assertTrue(result.contains("0"));
    }

    @Test
    void testInfixExpression() {
        Doc left = Doc.text("x");
        Doc right = Doc.text("y");
        Doc infix = TlaDocuments.infixExpression(left, "+", right);
        String result = infix.render(80);
        
        assertEquals("x + y", result);
    }

    @Test
    void testParentheses() {
        Doc inner = Doc.text("x + y");
        Doc paren = TlaDocuments.parentheses(inner);
        String result = paren.render(80);
        
        assertEquals("(x + y)", result);
    }

    @Test
    void testLines() {
        Doc doc1 = Doc.text("line1");
        Doc doc2 = Doc.text("line2");
        Doc doc3 = Doc.text("line3");
        
        Doc lines = TlaDocuments.lines(doc1, doc2, doc3);
        String result = lines.render(80);
        
        String[] resultLines = result.split("\n");
        assertEquals(3, resultLines.length);
        assertEquals("line1", resultLines[0]);
        assertEquals("line2", resultLines[1]);
        assertEquals("line3", resultLines[2]);
    }

    @Test
    void testLinesWithList() {
        List<Doc> docs = Arrays.asList(
            Doc.text("first"),
            Doc.text("second")
        );
        
        Doc lines = TlaDocuments.lines(docs);
        String result = lines.render(80);
        
        String[] resultLines = result.split("\n");
        assertEquals(2, resultLines.length);
        assertEquals("first", resultLines[0]);
        assertEquals("second", resultLines[1]);
    }

    @Test
    void testEmptyLines() {
        Doc lines = TlaDocuments.lines(Collections.emptyList());
        String result = lines.render(80);
        
        assertEquals("", result);
    }

    @Test
    void testComment() {
        Doc comment = TlaDocuments.comment("This is a comment");
        String result = comment.render(80);
        
        assertEquals("\\* This is a comment", result);
    }

    @Test
    void testTheorem() {
        Doc expr = Doc.text("x >= 0");
        Doc theorem = TlaDocuments.theorem(expr);
        String result = theorem.render(80);
        
        assertTrue(result.contains("THEOREM"));
        assertTrue(result.contains("x >= 0"));
    }

    @Test
    void testDocumentComposition() {
        // Test combining multiple factory methods
        Doc header = TlaDocuments.moduleHeader("TestModule");
        Doc varDecl = TlaDocuments.variableDeclaration(Arrays.asList("x", "y"));
        Doc opDef = TlaDocuments.operatorDefinition("Inc", Doc.text("x + 1"));
        Doc footer = TlaDocuments.moduleFooter();
        
        Doc complete = TlaDocuments.lines(header, varDecl, opDef, footer);
        String result = complete.render(80);
        
        assertTrue(result.contains("---- MODULE TestModule ----"));
        assertTrue(result.contains("VARIABLES"));
        assertTrue(result.contains("Inc =="));
        assertTrue(result.contains("===="));
    }
}