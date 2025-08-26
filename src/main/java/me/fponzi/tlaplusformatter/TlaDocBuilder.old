package me.fponzi.tlaplusformatter;

import com.opencastsoftware.prettier4j.Doc;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import tla2sany.st.TreeNode;

import java.lang.invoke.MethodHandles;
import java.util.ArrayList;
import java.util.List;

/**
 * Converts SANY AST nodes to Wadler Doc objects for pretty printing.
 * This is the main converter that handles the translation from TLA+ parse tree
 * to printable documents.
 */
public class TlaDocBuilder {
    
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());
    
    // SANY node kind constants - from TLA+ tools source
    private static final int N_MODULE = 382;
    private static final int N_BEGIN_MODULE = 333;
    private static final int N_END_MODULE = 363;
    private static final int N_EXTENDS = 365;
    private static final int N_VARIABLE_DECLARATION = 426;
    private static final int N_OPERATOR_DEFINITION = 389;
    private static final int N_IDENTIFIER = 375;
    private static final int N_NUMBER = 387;
    private static final int N_THEOREM = 421;
    private static final int N_BODY = 336;
    
    // Looks like we have a different constant for body - let me add 334
    private static final int N_BODY2 = 334;
    
    // Different EXTENDS constant found in logs - add 350
    private static final int N_EXTENDS2 = 350;
    
    private final FormatConfig config;
    
    public TlaDocBuilder(FormatConfig config) {
        this.config = config;
    }
    
    /**
     * Builds a Doc from a SANY TreeNode
     */
    public Doc build(TreeNode node) {
        if (node == null) {
            return Doc.empty();
        }
        
        return buildNode(node);
    }
    
    private Doc buildNode(TreeNode node) {
        int kind = node.getKind();
        
        switch (kind) {
            case N_MODULE:
                return buildModule(node);
            case N_BEGIN_MODULE:
                return buildBeginModule(node);
            case N_END_MODULE:
                return buildEndModule(node);
            case N_EXTENDS:
            case N_EXTENDS2:
                var e =  buildExtends(node);
                System.out.println(e);
                return e;
            case N_VARIABLE_DECLARATION:
                return buildVariableDeclaration(node);
            case N_OPERATOR_DEFINITION:
                return buildOperatorDefinition(node);
            case N_IDENTIFIER:
                return buildIdentifier(node);
            case N_NUMBER:
                return buildNumber(node);
            case N_THEOREM:
                return buildTheorem(node);
            case N_BODY:
            case N_BODY2:
                return buildBody(node);
            default:
                return buildGeneric(node);
        }
    }
    
    private Doc buildModule(TreeNode node) {
        if (node.zero() == null || node.zero().length == 0) {
            return Doc.empty();
        }
        
        List<Doc> parts = new ArrayList<>();
        
        // Process all module parts
        for (TreeNode child : node.zero()) {
            if (isValidNode(child)) {
                Doc childDoc = buildNode(child);
                if (!childDoc.equals(Doc.empty())) {
                    parts.add(childDoc);
                }
            }
        }
        
        return TlaDocuments.lines(parts);
    }
    
    private Doc buildBeginModule(TreeNode node) {
        if (node.zero() == null || node.zero().length < 2) {
            return Doc.text("---- MODULE Unknown ----");
        }
        
        String moduleName = node.zero()[1].getImage();
        return TlaDocuments.moduleHeader(moduleName);
    }
    
    private Doc buildEndModule(TreeNode node) {
        return TlaDocuments.moduleFooter();
    }
    
    private Doc buildExtends(TreeNode node) {
        List<String> modules = new ArrayList<>();
        
        // Check both zero() and one() arrays for modules
        TreeNode[] children = null;
        if (node.one() != null && node.one().length > 0) {
            children = node.one();
        } else if (node.zero() != null && node.zero().length > 0) {
            children = node.zero();
        }
        
        if (children == null) {
            return Doc.empty();
        }
        
        for (TreeNode child : children) {
            if (isValidNode(child) && !child.getImage().equals(",") && !child.getImage().equals("EXTENDS")) {
                modules.add(child.getImage());
            }
        }
        
        return TlaDocuments.extendsDeclaration(modules);
    }
    
    private Doc buildVariableDeclaration(TreeNode node) {
        List<String> variables = new ArrayList<>();
        
        // Variables are in node.one()
        if (node.one() != null) {
            for (TreeNode child : node.one()) {
                if (isValidNode(child) && !child.getImage().equals(",")) {
                    variables.add(child.getImage());
                }
            }
        }
        
        return TlaDocuments.variableDeclaration(variables);
    }
    
    private Doc buildOperatorDefinition(TreeNode node) {
        if (node.one() == null || node.one().length < 3) {
            return buildGeneric(node);
        }
        
        // node.one()[0] is the operator name/signature
        // node.one()[1] is the "==" 
        // node.one()[2] is the expression
        TreeNode nameNode = node.one()[0];
        TreeNode exprNode = node.one()[2];
        
        String operatorName = getOperatorName(nameNode);
        Doc expression = buildNode(exprNode);
        
        return TlaDocuments.operatorDefinition(operatorName, expression);
    }
    
    private String getOperatorName(TreeNode nameNode) {
        if (nameNode.zero() != null && nameNode.zero().length > 0) {
            return nameNode.zero()[0].getImage();
        }
        return nameNode.getImage();
    }
    
    private Doc buildIdentifier(TreeNode node) {
        return Doc.text(node.getImage());
    }
    
    private Doc buildNumber(TreeNode node) {
        return Doc.text(node.getImage());
    }
    
    private Doc buildTheorem(TreeNode node) {
        if (node.one() != null && node.one().length > 0) {
            Doc expression = buildNode(node.one()[0]);
            return TlaDocuments.theorem(expression);
        }
        return Doc.text("THEOREM");
    }
    
    private Doc buildBody(TreeNode node) {
        // Body contains the module contents between header and footer
        if (node.zero() == null || node.zero().length == 0) {
            return Doc.empty();
        }
        
        List<Doc> parts = new ArrayList<>();
        
        for (TreeNode child : node.zero()) {
            if (isValidNode(child)) {
                Doc childDoc = buildNode(child);
                if (!childDoc.equals(Doc.empty())) {
                    parts.add(childDoc);
                }
            }
        }
        
        return TlaDocuments.lines(parts);
    }
    
    private Doc buildGeneric(TreeNode node) {
        String image = node.getImage();
        
        // Log unknown node types to help debug
        if (image != null && image.startsWith("N_")) {
            LOG.debug("Generic node kind: {} image: '{}'", node.getKind(), image);
        }
        
        if (image != null && !image.isEmpty() && !image.startsWith("N_")) {
            return Doc.text(image);
        }
        
        // If no meaningful image, try to build from children
        List<Doc> children = new ArrayList<>();
        
        if (node.zero() != null) {
            for (TreeNode child : node.zero()) {
                if (isValidNode(child)) {
                    Doc childDoc = buildNode(child);
                    if (!childDoc.equals(Doc.empty())) {
                        children.add(childDoc);
                    }
                }
            }
        }
        
        if (node.one() != null) {
            for (TreeNode child : node.one()) {
                if (isValidNode(child)) {
                    Doc childDoc = buildNode(child);
                    if (!childDoc.equals(Doc.empty())) {
                        children.add(childDoc);
                    }
                }
            }
        }
        
        if (children.isEmpty()) {
            return Doc.empty();
        }
        
        // Join children with spaces
        Doc result = children.get(0);
        for (int i = 1; i < children.size(); i++) {
            result = result.appendSpace(children.get(i));
        }
        
        return result;
    }
    
    /**
     * Checks if a node is valid (has a real location, not a placeholder)
     */
    private boolean isValidNode(TreeNode node) {
        if (node == null) {
            return false;
        }
        
        // SANY creates placeholder nodes with MAX_VALUE coordinates
        return node.getLocation() != null && 
               node.getLocation().beginLine() != Integer.MAX_VALUE;
    }
}