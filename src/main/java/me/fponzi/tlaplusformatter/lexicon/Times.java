package me.fponzi.tlaplusformatter.lexicon;

import me.fponzi.tlaplusformatter.FormattedSpec;
import me.fponzi.tlaplusformatter.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;

public class Times extends TreeNode {
    public static final String IMAGE = "N_Times";
    public static final int KIND = 349;
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public Times(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        var z = this.zero();
        z[0].format(f);
        f.space(); //
        z[1].format(f); // \X
        f.space();
        z[2].format(f); // Y
    }


}
