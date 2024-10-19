package me.fponzi.tlaplusformatter.format.lexicon;

import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.invoke.MethodHandles;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.stream.Stream;

public class GenericTreeNode extends TreeNode {
    public static final int KIND = -1;
    public static final String IMAGE = "Generic";
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());
    private static final Map<Integer, String> SYMBOLS = new HashMap<>();
    static {
        SYMBOLS.put(87, ",");
        SYMBOLS.put(88, ":");
        SYMBOLS.put(90, ".");
        SYMBOLS.put(91, ".");
        SYMBOLS.put(93, "(");
        SYMBOLS.put(94, ")");
        SYMBOLS.put(95, ")");
        SYMBOLS.put(96, "[");
        SYMBOLS.put(97, "]_");
        SYMBOLS.put(99, "]");
        SYMBOLS.put(101, "{");
        SYMBOLS.put(102, "}");
        SYMBOLS.put(103, "<<");
        SYMBOLS.put(105, ">>");
        SYMBOLS.put(106, "!");
        SYMBOLS.put(107, "->");
        SYMBOLS.put(109, "|->");
        SYMBOLS.put(111, ""); // any number
        SYMBOLS.put(122, "[]"); // similar to 401?
        SYMBOLS.put(132, "/");
        SYMBOLS.put(195, "**");
        SYMBOLS.put(294, ""); // any identifier, like `counter`
        SYMBOLS.put(373, "-");
        SYMBOLS.put(397, "'");
        SYMBOLS.put(401, "[]");
        SYMBOLS.put(428, "=");
        SYMBOLS.put(418, ""); // any string, like `"MCCRDT"`
    }

    public GenericTreeNode(tla2sany.st.TreeNode node) {
        super(node);
    }

    @Override
    public void format(FormattedSpec f) {
        if (node == null) {
            return;
        }
        if (Stream.of("EXCEPT", "UNCHANGED", "UNION", "SUBSET", "DOMAIN", "INSTANCE").anyMatch(p -> node.getImage().equals(p))) {
            f.append(this).space();
            return;
        } else if (node.getImage().equals("N_GeneralId")
                || node.getImage().equals("N_GenPostfixOp")
                || node.getImage().equals("N_GenInfixOp")) {
            // this might have as image an identifier like "Nat"
            // but also an idPrefix in pos [0] and identifier in [1], like for !Nat.
            // In this case it's easier to just delegate to basePrintTree
            for (var child : this.zero()) {
                child.format(f);
            }
            return;
        }

        if (SYMBOLS.containsKey(this.getKind())) {
            // generically handle the symbols
            f.append(this);
            return;
        }

        LOG.debug("Unhandled: {}, {}, {}, {}", this.getImage(), this.getKind(), Arrays.toString(this.node.zero()), Arrays.toString(this.node.one()));

        if (!this.getImage().startsWith("N_")) {
            f.append(this);
        }
        if (this.zero() != null) {
            for (var child : this.zero()) {
                child.format(f);
            }
        }
        if (this.one() != null) {
            for (var child : this.one()) {
                child.format(f);
            }
        }

    }
}
