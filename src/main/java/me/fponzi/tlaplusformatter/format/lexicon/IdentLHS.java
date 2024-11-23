package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;
import java.util.List;
import java.util.Objects;

/**
 * Example: Left hand of operator definition
 * Move(from, to, disk) = ....
 */
public class IdentLHS extends TreeNode {
    public static final String IMAGE = "N_IdentLHS";
    public static final int KIND = 366;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());


    public IdentLHS(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        var z = zero();
        for (int i = 0; i < z.length; i++) {
            var ch = z[i];
            ch.format(f);
            if (i + 1 < z.length
                    && !(List.of(",", "(", ")").contains(z[i + 1].getImage()))
                    && !Objects.equals("(", ch.getImage())) {
                f.space();
            } else if (ch.getImage().equals(",")) f.space();
        }
    }
}
