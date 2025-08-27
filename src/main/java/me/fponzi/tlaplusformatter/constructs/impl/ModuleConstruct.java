package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.NodeKind;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

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
        public int getSupportedNodeKind() {
            return NodeKind.MODULE.getId();
        }

        @Override
        public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
            if (node.zero() == null || node.zero().length == 0) {
                return Doc.empty();
            }

            Doc p = null;
            TreeNode[] children = node.zero();

            // Process all module parts
            for (int i = 0; i < children.length; i++) {
                TreeNode child = children[i];
                if (context.isValidNode(child)) {
                    Doc childDoc = context.buildChild(child);
                    if (childDoc.equals(Doc.empty())) {
                        continue;
                    }
                    p = p == null ? childDoc : p.appendLine(childDoc);

                    if (i == children.length - 1) {
                        continue;
                    }
                    // Add preserved spacing after this node (except for the last one)
                    Doc spacing = context.getSpacingAfter(child, children[i + 1]);
                    if (spacing != null) {
                        p = p.appendLine(spacing);
                    }
                }
            }

            return p;
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
        public int getSupportedNodeKind() {
            return NodeKind.BEGIN_MODULE.getId();
        }

        @Override
        public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
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
        public int getSupportedNodeKind() {
            return NodeKind.END_MODULE.getId();
        }

        @Override
        public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
            return Doc.text(node.getHumanReadableImage());
        }
    }

    /**
     * Handles BODY (module body content).
     */
    public static class BodyConstruct extends ModuleMainConstruct {

        @Override
        public String getName() {
            return "BODY";
        }

        @Override
        public int getSupportedNodeKind() {
            return NodeKind.BODY.getId();
        }
    }
}