package me.fponzi.tlaplusformatter;

import com.opencastsoftware.prettier4j.Doc;
import com.opencastsoftware.prettier4j.RenderOptions;
import me.fponzi.tlaplusformatter.exceptions.SanyFrontendException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import tla2sany.st.TreeNode;

import java.io.File;
import java.io.IOException;
import java.lang.invoke.MethodHandles;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class TLAPlusFormatter {
    private static final Logger LOG = LoggerFactory.getLogger(MethodHandles.lookup().lookupClass());

    private final TreeNode root;
    private final File spec;
    private final TlaDocBuilder docBuilder;
    private String output;

    public TLAPlusFormatter(File specPath) throws IOException, SanyFrontendException {
        this(specPath, new FormatConfig());
    }
    
    public TLAPlusFormatter(File specPath, FormatConfig config) throws IOException, SanyFrontendException {
        this.docBuilder = new TlaDocBuilder(config);
        this.root = SANYWrapper.load(specPath);
        this.spec = specPath;

        format();
    }

    public String getOutput() {
        return output;
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
        this(storeToTmp(spec), new FormatConfig());
    }
    
    public TLAPlusFormatter(String spec, FormatConfig config) throws IOException, SanyFrontendException {
        this(storeToTmp(spec), config);
    }

    private void format() throws IOException {
        String[] extraSections = getPreAndPostModuleSectionsFromSpecFile(spec.toPath());
        
        // Pass original source to docBuilder for spacing preservation
        String originalSource = Files.readString(spec.toPath());
        docBuilder.setOriginalSource(originalSource);
        
        Doc moduleDoc = docBuilder.build(root);
        System.out.println("rendering output");
        this.output = extraSections[0] +
                          moduleDoc.render(RenderOptions.defaults()) +
                          extraSections[1];
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
        for (int i = 0; i < startLine - 1; i++) {
            preModuleSection.append(lines[i]).append(System.lineSeparator());
        }
        for (int i = endLine; i < lines.length; i++) {
            postModuleSection.append(System.lineSeparator()).append(lines[i]);
        }
        if(spec.endsWith("\n")) {
            postModuleSection.append(System.lineSeparator());
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
