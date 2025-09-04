package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.*;
import tla2sany.st.TreeNode;

import java.util.List;

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
    public int getSupportedNodeKind() {
        return NodeKind.EXTENDS.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        List<String> modules = context.extractStringList(node);
        Doc prefix = context.buildChild(node.zero()[0]); // "EXTENDS" keyword
        return new ExtendsFormatter(context.getConfig()).format(prefix, modules);
    }

    /**
     * Dedicated formatter for EXTENDS declarations.
     */
    private static class ExtendsFormatter extends BaseConstructFormatter<String> {

        public ExtendsFormatter(me.fponzi.tlaplusformatter.FormatConfig config) {
            super(config);
        }


        public Doc format(Doc prefix, List<String> extendedModules) {
            if (extendedModules.isEmpty()) {
                return Doc.empty();
            }
            ListFormatStrategy strategy = determineStrategy("EXTENDS", extendedModules.size());
            return formatList(extendedModules, prefix, stringFormatter(), strategy);
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
    }
}