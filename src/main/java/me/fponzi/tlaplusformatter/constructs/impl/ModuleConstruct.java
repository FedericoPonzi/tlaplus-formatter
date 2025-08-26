package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.*;
import tla2sany.st.TreeNode;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

/**
 * Construct implementations for module structure elements.
 */
public class ModuleConstruct {
    
    /**
     * Handles the main MODULE node.
     */
    public static class ModuleMainConstruct implements TlaConstruct {
        
        @Override
        public String getName() {
            return "MODULE";
        }
        
        @Override
        public Set<Integer> getSupportedNodeKinds() {
            return NodeKind.MODULE.getAllIds();
        }
        
        @Override
        public Doc buildDoc(TreeNode node, ConstructContext context) {
            if (node.zero() == null || node.zero().length == 0) {
                return Doc.empty();
            }
            
            List<Doc> parts = new ArrayList<>();
            TreeNode[] children = node.zero();
            
            // Process all module parts
            for (int i = 0; i < children.length; i++) {
                TreeNode child = children[i];
                if (context.isValidNode(child)) {
                    Doc childDoc = context.buildChild(child);
                    if (!childDoc.equals(Doc.empty())) {
                        parts.add(childDoc);
                        
                        // Add preserved spacing after this node (except for the last one)
                        if (i < children.length - 1) {
                            Doc spacing = context.getSpacingAfter(child);
                            if (!spacing.equals(Doc.empty())) {
                                parts.add(spacing);
                            }
                        }
                    }
                }
            }
            
            return createLines(parts);
        }
        
        private Doc createLines(List<Doc> parts) {
            if (parts.isEmpty()) {
                return Doc.empty();
            }
            
            Doc result = parts.get(0);
            for (int i = 1; i < parts.size(); i++) {
                result = result.appendLine(parts.get(i));
            }
            return result;
        }
    }
    
    /**
     * Handles BEGIN_MODULE (module header).
     */
    public static class BeginModuleConstruct implements TlaConstruct {
        
        @Override
        public String getName() {
            return "BEGIN_MODULE";
        }
        
        @Override
        public Set<Integer> getSupportedNodeKinds() {
            return NodeKind.BEGIN_MODULE.getAllIds();
        }
        
        @Override
        public Doc buildDoc(TreeNode node, ConstructContext context) {
            if (node.zero() == null || node.zero().length < 2) {
                return Doc.text("---- MODULE Unknown ----");
            }
            
            String moduleName = node.zero()[1].getImage();
            return createModuleHeader(moduleName);
        }
        
        private Doc createModuleHeader(String moduleName) {
            return Doc.text("---- MODULE ")
                    .append(Doc.text(moduleName))
                    .append(Doc.text(" ----"));
        }
    }
    
    /**
     * Handles END_MODULE (module footer).
     */
    public static class EndModuleConstruct implements TlaConstruct {
        
        @Override
        public String getName() {
            return "END_MODULE";
        }
        
        @Override
        public Set<Integer> getSupportedNodeKinds() {
            return NodeKind.END_MODULE.getAllIds();
        }
        
        @Override
        public Doc buildDoc(TreeNode node, ConstructContext context) {
            return Doc.text("====");
        }
    }
    
    /**
     * Handles BODY (module body content).
     */
    public static class BodyConstruct implements TlaConstruct {
        
        @Override
        public String getName() {
            return "BODY";
        }
        
        @Override
        public Set<Integer> getSupportedNodeKinds() {
            return NodeKind.BODY.getAllIds();
        }
        
        @Override
        public Doc buildDoc(TreeNode node, ConstructContext context) {
            // Body contains the module contents between header and footer
            if (node.zero() == null || node.zero().length == 0) {
                return Doc.empty();
            }
            
            List<Doc> parts = new ArrayList<>();
            TreeNode[] children = node.zero();
            
            for (int i = 0; i < children.length; i++) {
                TreeNode child = children[i];
                if (context.isValidNode(child)) {
                    Doc childDoc = context.buildChild(child);
                    if (!childDoc.equals(Doc.empty())) {
                        parts.add(childDoc);
                        
                        // Add preserved spacing after this node (except for the last one)
                        if (i < children.length - 1) {
                            Doc spacing = context.getSpacingAfter(child);
                            if (!spacing.equals(Doc.empty())) {
                                parts.add(spacing);
                            }
                        }
                    }
                }
            }
            
            return createLines(parts);
        }
        
        private Doc createLines(List<Doc> parts) {
            if (parts.isEmpty()) {
                return Doc.empty();
            }
            
            Doc result = parts.get(0);
            for (int i = 1; i < parts.size(); i++) {
                result = result.appendLine(parts.get(i));
            }
            return result;
        }
    }
}