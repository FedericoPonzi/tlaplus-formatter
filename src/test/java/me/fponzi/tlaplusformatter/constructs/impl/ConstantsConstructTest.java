package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.FormatConfig;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.junit.jupiter.MockitoExtension;
import tla2sany.st.TreeNode;

import java.util.Arrays;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class ConstantsConstructTest {

    private final ConstantsConstruct construct = new ConstantsConstruct();
    static private final int CONSTANT_KIND = 392;

    @Test
    void testGetName() {
        assertEquals("CONSTANTS", construct.getName());
    }

    @Test
    void testGetSupportedNodeKinds() {
        assertTrue(construct.getSupportedNodeKinds().contains(CONSTANT_KIND));
        assertEquals(NodeKind.CONSTANTS.getAllIds(), construct.getSupportedNodeKinds());
    }

    @Test
    void testGetPriority() {
        assertEquals(10, construct.getPriority());
    }

    @Test
    void testCanHandle() {
        TreeNode mockNode = mock(TreeNode.class);
        when(mockNode.getKind()).thenReturn(CONSTANT_KIND); // CONSTANTS node kind

        assertTrue(construct.canHandle(mockNode));

        when(mockNode.getKind()).thenReturn(999); // Unknown node kind
        assertFalse(construct.canHandle(mockNode));
    }

    @Test
    void testBuildDocSingleConstant() {
        // Setup mocks
        TreeNode mockNode = mock(TreeNode.class);
        ConstructContext mockContext = mock(ConstructContext.class);
        FormatConfig mockConfig = mock(FormatConfig.class);

        // Mock the context to return a single constant
        when(mockContext.extractStringList(mockNode)).thenReturn(List.of("N"));
        when(mockContext.getConfig()).thenReturn(mockConfig);

        // Execute
        Doc result = construct.buildDoc(mockNode, mockContext);

        // Verify
        assertNotNull(result);
        String rendered = result.render();
        assertTrue(rendered.contains("CONSTANT N"), "Should format single constant correctly");
    }

    @Test
    void testBuildDocMultipleConstants() {
        // Setup mocks
        TreeNode mockNode = mock(TreeNode.class);
        ConstructContext mockContext = mock(ConstructContext.class);
        FormatConfig mockConfig = mock(FormatConfig.class);

        // Mock the context to return multiple constants
        List<String> constants = Arrays.asList("N", "MaxValue", "DefaultState");
        when(mockContext.extractStringList(mockNode)).thenReturn(constants);
        when(mockContext.getConfig()).thenReturn(mockConfig);

        // Execute
        Doc result = construct.buildDoc(mockNode, mockContext);

        // Verify
        assertNotNull(result);
        String rendered = result.render();
        assertTrue(rendered.startsWith("CONSTANTS"), "Should start with CONSTANTS keyword");
        assertTrue(rendered.contains("N"), "Should contain first constant");
        assertTrue(rendered.contains("MaxValue"), "Should contain second constant");
        assertTrue(rendered.contains("DefaultState"), "Should contain third constant");
    }

    @Test
    void testBuildDocEmptyConstants() {
        // Setup mocks
        TreeNode mockNode = mock(TreeNode.class);
        ConstructContext mockContext = mock(ConstructContext.class);
        FormatConfig mockConfig = mock(FormatConfig.class);

        // Mock the context to return no constants
        when(mockContext.extractStringList(mockNode)).thenReturn(List.of());
        when(mockContext.getConfig()).thenReturn(mockConfig);

        // Execute
        Doc result = construct.buildDoc(mockNode, mockContext);

        // Verify
        assertNotNull(result);
        assertEquals("", result.render(), "Empty constants should produce empty output");
    }
}