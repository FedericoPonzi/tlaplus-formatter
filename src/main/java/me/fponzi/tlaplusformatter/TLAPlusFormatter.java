package me.fponzi.tlaplusformatter;

import me.fponzi.tlaplusformatter.exceptions.SanyFrontendException;
import me.fponzi.tlaplusformatter.format.FactoryRegistry;
import me.fponzi.tlaplusformatter.format.FormattedSpec;
import me.fponzi.tlaplusformatter.format.TreeNode;
import me.fponzi.tlaplusformatter.format.lexicon.TlaModule;
import org.reflections.Reflections;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.File;
import java.io.IOException;
import java.lang.invoke.MethodHandles;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class TLAPlusFormatter {
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    public FormattedSpec f;
    TreeNode root;
    File spec;

    public TLAPlusFormatter(File specPath) throws IOException, SanyFrontendException {
        root = SANYWrapper.load(specPath);
        this.spec = specPath;

        // Use Reflections library to find all classes that extend TreeNode
        Reflections reflections = new Reflections("me.fponzi.tlaplusformatter.format.lexicon");
        Set<Class<? extends TreeNode>> classes = reflections.getSubTypesOf(TreeNode.class);
        for (Class<? extends TreeNode> clazz : classes) {
            FactoryRegistry.register(clazz);
        }
        format();
    }

    public String getOutput() {
        return f.getOut().toString();
    }

    /**
     * Create a new instance of the formatter from a string containing the spec.
     * The spec is written to a temporary file, which is then passed to SANY.
     * The temporary file is deleted after the formatting is complete.
     * <p>
     * Safety: The input spec should be called "Spec" otherwise SANY will complain.
     *
     * @param spec
     * @throws IOException
     */
    public TLAPlusFormatter(String spec) throws IOException, SanyFrontendException {
        this(storeToTmp(spec));
    }

    private void format() throws IOException {
        f = new FormattedSpec();
        var extraSections = getPreAndPostModuleSectionsFromSpecFile(spec.toPath());
        assert root.getKind() == TlaModule.KIND;
        f.append(extraSections[0]);
        root.format(f);
        f.append(extraSections[1]);
    }

    static String getModuleName(String spec) {
        String regex = "----\\s?MODULE\\s+(\\w+)\\s?----";
        Pattern pattern = Pattern.compile(regex);
        Matcher matcher = pattern.matcher(spec);

        // Find the first match
        if (matcher.find()) {
            return matcher.group(1);
        } else {
            return "Spec";
        }
    }

    private static File storeToTmp(String spec) throws IOException {
        File tmpFolder = Files.createTempDirectory("sanyimp").toFile();
        var fileName = getModuleName(spec) + ".tla";
        File tmpFile = new File(tmpFolder, fileName);
        try (java.io.FileWriter writer = new java.io.FileWriter(tmpFile)) {
            writer.write(spec);
        }
        return tmpFile;
    }

    private String[] getPreAndPostModuleSections(String spec, int startLine, int endLine) {
        String[] lines = spec.split("\\R"); // Split by any line terminator
        StringBuilder preModuleSection = new StringBuilder();
        StringBuilder postModuleSection = new StringBuilder();

        for (int i = 0; i < lines.length; i++) {
            if (i < startLine - 1) {
                preModuleSection.append(lines[i]).append(System.lineSeparator());
            } else if (i > endLine - 1) {
                postModuleSection.append(lines[i]).append(System.lineSeparator());
            }
        }
        return new String[]{preModuleSection.toString(), postModuleSection.toString()};
    }

    private String[] getPreAndPostModuleSectionsFromSpecFile(Path spec) throws IOException {
        try {
            String content = Files.readString(spec);
            //read all the content of spec:
            var startOfModuleRow = root.zero()[0].getLocation().getCoordinates()[0];
            var endOfModuleRow = root.zero()[3].getLocation().getCoordinates()[0];
            return getPreAndPostModuleSections(content, startOfModuleRow, endOfModuleRow);
        } catch (IOException e) {
            LOG.error("Failed to read content of the spec to get pre and post module sections: {}", String.valueOf(e));
            throw e;
        }
    }


}
