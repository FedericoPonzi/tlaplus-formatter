package me.fponzi.tlaplusformatter.format;

import me.fponzi.tlaplusformatter.format.lexicon.GenericTreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.HashMap;
import java.util.Map;

public class FactoryRegistry {
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());
    private static final Map<Integer, TreeNodeFactory<? extends TreeNode>> registry = new HashMap<>();

    public static void register(Class<? extends TreeNode> clazz) {
        if (Modifier.isAbstract(clazz.getModifiers())) {
            // skip registering abstract classes.
            return;
        }
        try {
            Field kindField = clazz.getField("KIND");
            try {
                int kind = kindField.getInt(null); // Access static field
                registry.put(kind, new TreeNodeFactory<>(clazz));

            } catch(NullPointerException e) {
                throw new RuntimeException(String.format("Error: class %s is missing field KIND.", clazz.getName()));
            }
        } catch (NoSuchFieldException | IllegalAccessException e) {
            throw new RuntimeException("Failed to register class: " + clazz.getSimpleName(), e);
        }
    }

    public static TreeNode createInstance(int kindNumber, tla2sany.st.TreeNode node) {
        TreeNodeFactory<? extends TreeNode> factory = registry.get(kindNumber);
        if (factory != null) {
            LOG.debug("Found facotry: {}", factory.createInstance(node).getClass().getSimpleName());
            return factory.createInstance(node);
        } else {
            //LOG.debug("No factory registered for kind number: " + kindNumber);
            return new GenericTreeNode(node);
        }
    }
}
