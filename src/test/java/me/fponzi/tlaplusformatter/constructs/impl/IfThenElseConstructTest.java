package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.FormatConfig;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.junit.jupiter.MockitoExtension;
import tla2sany.st.TreeNode;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class IfThenElseConstructTest {

    private final IfThenElseConstruct construct = new IfThenElseConstruct();
    static private final int IF_THEN_ELSE_KIND = 369;

    @Test
    void testGetName() {
        assertEquals("IF_THEN_ELSE", construct.getName());
    }

    @Test
    void testCanHandle() {
        TreeNode mockNode = mock(TreeNode.class);
        when(mockNode.getKind()).thenReturn(IF_THEN_ELSE_KIND);

        assertTrue(construct.canHandle(mockNode));

        when(mockNode.getKind()).thenReturn(999); // Unknown node kind
        assertFalse(construct.canHandle(mockNode));
    }

    @Test
    void testBuildDocValidStructure() {
        // Setup mocks for IF-THEN-ELSE structure using lenient mode
        TreeNode mockNode = mock(TreeNode.class, withSettings().lenient());
        ConstructContext mockContext = mock(ConstructContext.class, withSettings().lenient());
        FormatConfig mockConfig = mock(FormatConfig.class, withSettings().lenient());

        // Mock the zero children array (6 elements as expected)
        TreeNode[] zeroChildren = new TreeNode[6];
        zeroChildren[0] = mock(TreeNode.class);  // IF keyword
        zeroChildren[1] = mock(TreeNode.class);  // condition
        zeroChildren[2] = mock(TreeNode.class);  // THEN keyword
        zeroChildren[3] = mock(TreeNode.class);  // then expression
        zeroChildren[4] = mock(TreeNode.class);  // ELSE keyword
        zeroChildren[5] = mock(TreeNode.class);  // else expression

        when(mockNode.zero()).thenReturn(zeroChildren);
        when(mockNode.getKind()).thenReturn(IF_THEN_ELSE_KIND);

        // Mock context behavior (only the ones we actually use)
        when(mockContext.buildChild(zeroChildren[1])).thenReturn(Doc.text("x > 5"));
        when(mockContext.buildChild(zeroChildren[3])).thenReturn(Doc.text("x + 1"));
        when(mockContext.buildChild(zeroChildren[5])).thenReturn(Doc.text("0"));
        when(mockContext.getConfig()).thenReturn(mockConfig);
        when(mockConfig.getIndentSize()).thenReturn(4);

        // Execute
        Doc result = construct.buildDoc(mockNode, mockContext, 4);

        // Verify
        assertNotNull(result);
        String rendered = result.render();
        assertTrue(rendered.contains("IF x > 5"), "Should contain IF condition");
        assertTrue(rendered.contains("THEN x + 1"), "Should contain THEN expression");
        assertTrue(rendered.contains("ELSE 0"), "Should contain ELSE expression");
    }

    @Test
    void testStaticUtilityMethod() {
        // Test the static utility method
        Doc condition = Doc.text("x > 0");
        Doc thenExpr = Doc.text("x");
        Doc elseExpr = Doc.text("-x");

        Doc result = IfThenElseConstruct.create(condition, thenExpr, elseExpr, 2);

        assertNotNull(result);
        String rendered = result.render();
        assertTrue(rendered.contains("IF x > 0"), "Should contain condition");
        assertTrue(rendered.contains("THEN"), "Should contain THEN");
        assertTrue(rendered.contains("ELSE"), "Should contain ELSE");
    }

}