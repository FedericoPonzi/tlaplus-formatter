package me.fponzi.tlaplusformatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.TlaDocBuilder;
import me.fponzi.tlaplusformatter.constructs.ConstructContext;
import me.fponzi.tlaplusformatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.List;
import java.util.Optional;

public abstract class AbstractAppendImageConstruct implements TlaConstruct {
    public abstract int getSupportedNodeKind();

    public abstract String getName();

    @Override
    public final Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        var o = node.one();
        if ((z == null || z.length == 0) && (o == null || o.length == 0)) {
            return Doc.text(TlaDocBuilder.getBestImage(node));
        }
        return Optional.ofNullable(buildChildren(node, context, z)).orElse(buildChildren(node, context, o));
    }

    private Doc buildChildren(TreeNode node, ConstructContext context, TreeNode[] c) {
        if (c == null) {
            return null;
        }
        var childDoc = context.buildChild(c[0]);
        for (int i = 1; i < c.length; i++) {
            var nextChildDoc = context.buildChild(c[i]);
            if (childDoc == Doc.empty()) {
                childDoc = nextChildDoc;
            } else if (nextChildDoc != null && nextChildDoc != Doc.empty()) {
                // don't add space before or after , ] ) } [ ( {
                var skipSpace = List.of(",", "]", ")", "}", "(", "[", "{");
                var prevImage = c[i - 1].getHumanReadableImage();
                var currImage = c[i].getHumanReadableImage();
                // Skip space after module prefix (e.g., "R!" in "R!Nat")
                var shouldSkipSpace = skipSpace.contains(currImage)
                        || skipSpace.contains(prevImage) // to format `f(_)`
                        || (prevImage != null && prevImage.endsWith("!")); // module prefix like R!
                if (shouldSkipSpace) {
                    childDoc = childDoc.append(nextChildDoc);
                } else {
                    childDoc = childDoc.appendSpace(nextChildDoc);
                }
            }
        }
        return childDoc;
    }
}
