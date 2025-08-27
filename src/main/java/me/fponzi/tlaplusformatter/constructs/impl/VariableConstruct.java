package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.*;
import tla2sany.st.TreeNode;

import java.util.List;

/**
 * Construct implementation for VARIABLE/VARIABLES declarations.
 */
public class VariableConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "VARIABLES";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.VARIABLE_DECLARATION.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        List<String> variables = context.extractStringList(node);
        return new VariableFormatter(context.getConfig()).format(variables);
    }

    /**
     * Dedicated formatter for VARIABLE declarations.
     */
    private static class VariableFormatter extends BaseConstructFormatter<String> {

        public VariableFormatter(me.fponzi.tlaplusformatter.FormatConfig config) {
            super(config);
        }

        public Doc format(List<String> variables) {
            if (variables.isEmpty()) {
                return Doc.empty();
            }

            String prefix = variables.size() == 1 ? "VARIABLE " : "VARIABLES ";
            ListFormatStrategy strategy = determineStrategy("VARIABLES", variables.size());

            return formatList(variables, prefix, stringFormatter(), strategy);
        }

        @Override
        protected ListFormatStrategy determineStrategy(String constructName, int itemCount) {
            // For VARIABLES, prefer single line for short lists
            if (itemCount <= 3) {
                return ListFormatStrategy.SINGLE_LINE;
            } else {
                return config.getConstructSetting(
                        constructName, "breakStrategy", ListFormatStrategy.SMART_BREAK);
            }
        }
    }
}