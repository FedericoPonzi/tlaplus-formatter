package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.constructs.*;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import tla2sany.st.TreeNode;

import java.lang.invoke.MethodHandles;
import java.util.List;

/**
 * Construct implementation for CONSTANTS declarations.
 * Handles formatting of "CONSTANTS x, y, z" constructs.
 */
public class ConstantsConstruct implements TlaConstruct {
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    @Override
    public String getName() {
        return "CONSTANTS";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.CONS_DECL.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context) {
        LOG.debug("ConstantsConstruct::buildDoc called with note: {} context: {}", node, context);
        List<String> constants = context.extractStringList(node);
        LOG.debug("Extracted constants: {}", constants);
        return new ConstantsFormatter(context.getConfig()).format(constants);
    }

    /**
     * Dedicated formatter for CONSTANTS declarations.
     */
    private static class ConstantsFormatter extends BaseConstructFormatter<String> {

        public ConstantsFormatter(me.fponzi.tlaplusformatter.FormatConfig config) {
            super(config);
        }

        public Doc format(List<String> constants) {
            if (constants.isEmpty()) {
                return Doc.empty();
            }
            String prefix = constants.size() == 1 ? "CONSTANT " : "CONSTANTS ";
            ListFormatStrategy strategy = determineStrategy("CONSTANTS", constants.size());
            return formatList(constants, prefix, stringFormatter(), strategy);
        }

        @Override
        protected ListFormatStrategy determineStrategy(String constructName, int itemCount) {
            // For CONSTANTS, use smart breaks for longer lists
            if (itemCount <= 3) {
                return ListFormatStrategy.SINGLE_LINE;
            } else {
                return config.getConstructSetting(
                        constructName, "breakStrategy", ListFormatStrategy.SMART_BREAK);
            }
        }
    }
}