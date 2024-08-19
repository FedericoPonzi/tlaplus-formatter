package me.fponzi.tlaplusformatter;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import tla2sany.st.Location;

import java.lang.invoke.MethodHandles;

public abstract class TreeNode implements Formattable  {
    tla2sany.st.TreeNode node;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());


    public TreeNode(tla2sany.st.TreeNode node) {
        this.node = node;
    }

    private static TreeNode[] toInternal(tla2sany.st.TreeNode[] node) {
        if(node == null) {
            return null;
        }
        TreeNode[] ret = new TreeNode[node.length];
        var factory = new FactoryRegistry();

        for (int i = 0; i < ret.length; i++) {

            ret[i] = factory.createInstance(node[i].getKind(), node[i]);
        }
        return ret;
    }

    public TreeNode[] zero() {
        return toInternal(node.zero());
    }

    public TreeNode[] one() {
        return toInternal(node.one());
    }

    public String[] getPreComments() {
        return node.getPreComments();
    }

    public String getImage() {
        return node.getImage();
    }
    public Location getLocation() {
        return node.getLocation();
    }

    public int getKind() {
        return node.getKind();
    }
}
