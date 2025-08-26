package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.*;
import tla2sany.st.TreeNode;

import java.util.List;
import java.util.Set;

/**
 * Construct implementation for CONSTANTS declarations.
 * Handles formatting of "CONSTANTS x, y, z" constructs.
 */
public class ConstantsConstruct implements TlaConstruct {
    
    @Override
    public String getName() {
        return "CONSTANTS";
    }
    
    @Override
    public Set<Integer> getSupportedNodeKinds() {
        return NodeKind.CONSTANTS.getAllIds();
    }
    
    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context) {
        // For CONSTANTS nodes with no children, just return the keyword
        // The actual constants appear to be handled separately by SANY
        if (node.getImage() != null && node.getImage().equals("CONSTANTS")) {
            return Doc.text("CONSTANTS");
        }
        
        // Fallback to normal processing
        List<String> constants = context.extractStringList(node);
        return new ConstantsFormatter(context.getConfig()).format(constants);
    }
    
    @Override
    public int getPriority() {
        return 10; // Higher priority for CONSTANTS handling
    }
    
    /**
     * Dedicated formatter for CONSTANTS declarations.
     */
    private static class ConstantsFormatter extends BaseConstructFormatter<String> {
        
        public ConstantsFormatter(me.fponzi.tlaplusformatter.FormatConfig config) {
            super(config);
        }
        
        /**
         * Main formatting method for CONSTANTS declarations.
         */
        public Doc format(List<String> constants) {
            if (constants.isEmpty()) {
                return Doc.empty();
            }
            
            if (constants.size() == 1) {
                return formatSingle(constants.get(0));
            }
            
            return formatMultiple(constants);
        }
        
        @Override
        protected Doc formatSingle(String constant) {
            return Doc.text("CONSTANTS ").append(Doc.text(constant));
        }
        
        @Override
        protected Doc formatMultiple(List<String> constants) {
            ListFormatStrategy strategy = determineStrategy("CONSTANTS", constants.size());
            return formatList(constants, "CONSTANTS ", stringFormatter(), strategy);
        }
        
        @Override
        protected ListFormatStrategy determineStrategy(String constructName, int itemCount) {
            // For CONSTANTS, use smart breaks for longer lists
            if (itemCount <= 4) {
                return ListFormatStrategy.SINGLE_LINE;
            } else {
                return config.getConstructSetting(
                    constructName, "breakStrategy", ListFormatStrategy.SMART_BREAK);
            }
        }
    }
}