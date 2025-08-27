package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.*;
import tla2sany.st.TreeNode;

import java.util.List;
import java.util.Set;

/**
 * Construct implementation for EXTENDS declarations.
 * Handles formatting of module import lists with smart line breaking.
 */
public class ExtendsConstruct implements TlaConstruct {
    
    @Override
    public String getName() {
        return "EXTENDS";
    }
    
    @Override
    public Set<Integer> getSupportedNodeKinds() {
        return NodeKind.EXTENDS.getAllIds();
    }
    
    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context) {
        List<String> modules = context.extractStringList(node);
        return new ExtendsFormatter(context.getConfig()).format(modules);
    }
    
    @Override
    public int getPriority() {
        return 10; // Higher priority for EXTENDS handling
    }
    
    /**
     * Dedicated formatter for EXTENDS declarations.
     */
    private static class ExtendsFormatter extends BaseConstructFormatter<String> {
        
        public ExtendsFormatter(me.fponzi.tlaplusformatter.FormatConfig config) {
            super(config);
        }
        
        /**
         * Main formatting method for EXTENDS declarations.
         */
        public Doc format(List<String> modules) {
            if (modules.isEmpty()) {
                return Doc.empty();
            }
            
            // Use custom grouping for EXTENDS to match expected behavior
            return formatExtendsWithGrouping(modules);
        }
        
        @Override
        protected ListFormatStrategy determineStrategy(String constructName, int itemCount) {
            // For EXTENDS, use smart breaks for longer lists
            if (itemCount <= 3) {
                return ListFormatStrategy.SINGLE_LINE;
            } else {
                return config.getConstructSetting(
                    constructName, "breakStrategy", ListFormatStrategy.SMART_BREAK);
            }
        }
        
        private String getName() {
            return "EXTENDS";
        }
        
        /**
         * Custom formatting for EXTENDS that groups modules intelligently.
         */
        private Doc formatExtendsWithGrouping(List<String> modules) {
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
            
            // Use group to enable line breaking with proper indentation
            return Doc.group(
                Doc.text("EXTENDS ")
                    .append(moduleList.indent("EXTENDS ".length()))
            );
        }
    }
}