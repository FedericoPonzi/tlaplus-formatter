package me.fponzi.tlaplusformatter;

import java.lang.reflect.Constructor;

public class TreeNodeFactory<T extends TreeNode>  {

    private final Constructor<T> constructor;

    public TreeNodeFactory(Class<T> clazz) {
        try {
            this.constructor = clazz.getConstructor(tla2sany.st.TreeNode.class);
        } catch (NoSuchMethodException e) {
            throw new RuntimeException("Constructor not found", e);
        }
    }

    public T createInstance(tla2sany.st.TreeNode node) {
        try {
            return constructor.newInstance(node);
        } catch (Exception e) {
            throw new RuntimeException("Failed to create instance", e);
        }
    }
}
