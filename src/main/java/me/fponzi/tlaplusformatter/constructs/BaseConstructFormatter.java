package me.fponzi.tlaplusformatter.constructs;

import com.opencastsoftware.prettier4j.Doc;
import me.fponzi.tlaplusformatter.FormatConfig;

import java.util.List;
import java.util.function.Function;

/**
 * Base class for construct formatters providing common formatting patterns.
 * This eliminates code duplication and provides consistent formatting strategies.
 *
 * @param <T> The type of items being formatted (e.g., String for module names)
 */
public abstract class BaseConstructFormatter<T> {

    protected final FormatConfig config;

    public BaseConstructFormatter(FormatConfig config) {
        this.config = config;
    }

    /**
     * Format a list of items with a prefix using the specified strategy.
     *
     * @param items         List of items to format
     * @param prefix        Prefix string (e.g., "EXTENDS ", "VARIABLES ")
     * @param itemFormatter Function to convert items to Doc objects
     * @param strategy      Formatting strategy to use
     * @return Doc object for the entire construct
     */
    protected Doc formatList(List<T> items, String prefix,
                             Function<T, Doc> itemFormatter,
                             ListFormatStrategy strategy) {

        if (items.isEmpty()) {
            return Doc.empty();
        }

        if (items.size() == 1) {
            return Doc.text(prefix).append(itemFormatter.apply(items.get(0)));
        }

        switch (strategy) {
            case SINGLE_LINE:
                return formatAsSingleLine(items, prefix, itemFormatter);
            case SMART_BREAK:
                return formatWithSmartBreaks(items, prefix, itemFormatter);
            case ALWAYS_BREAK:
                return formatWithLineBreaks(items, prefix, itemFormatter);
            default:
                throw new IllegalArgumentException("Unknown strategy: " + strategy);
        }
    }

    /**
     * Format items as a single line with comma separation.
     */
    protected Doc formatAsSingleLine(List<T> items, String prefix, Function<T, Doc> itemFormatter) {
        Doc result = Doc.text(prefix).append(itemFormatter.apply(items.get(0)));

        for (int i = 1; i < items.size(); i++) {
            result = result.append(Doc.text(", ")).append(itemFormatter.apply(items.get(i)));
        }

        return result;
    }

    /**
     * Format items with smart line breaking based on line width.
     * Uses prettier4j's line-or-space mechanism for optimal breaking.
     */
    protected Doc formatWithSmartBreaks(List<T> items, String prefix, Function<T, Doc> itemFormatter) {
        Doc itemList = itemFormatter.apply(items.get(0));

        for (int i = 1; i < items.size(); i++) {
            itemList = itemList
                    .append(Doc.text(","))
                    .appendLineOrSpace(itemFormatter.apply(items.get(i)));
        }

        // Use group to enable line breaking with proper indentation
        return Doc.group(
                Doc.text(prefix)
                        .appendLineOrSpace(itemList.indent(prefix.length()))
        );
    }

    /**
     * Format items with line breaks after each item.
     * Each item goes on its own line with proper indentation.
     */
    protected Doc formatWithLineBreaks(List<T> items, String prefix, Function<T, Doc> itemFormatter) {
        Doc result = Doc.text(prefix).append(itemFormatter.apply(items.get(0)));

        for (int i = 1; i < items.size(); i++) {
            result = result
                    .append(Doc.text(","))
                    .appendLine(itemFormatter.apply(items.get(i)).indent(prefix.length()));
        }

        return result;
    }

    /**
     * Create a simple text formatter for string items.
     */
    protected static Function<String, Doc> stringFormatter() {
        return Doc::text;
    }

    /**
     * Create a formatter that wraps items with a prefix/suffix.
     */
    protected static <T> Function<T, Doc> wrappedFormatter(String prefix, String suffix,
                                                           Function<T, Doc> innerFormatter) {
        return item -> Doc.text(prefix)
                .append(innerFormatter.apply(item))
                .append(Doc.text(suffix));
    }

    /**
     * Determine appropriate formatting strategy based on list size and configuration.
     */
    protected ListFormatStrategy determineStrategy(String constructName, int itemCount) {
        // Check construct-specific settings
        ListFormatStrategy configuredStrategy = config.getConstructSetting(
                constructName, "breakStrategy", null);

        if (configuredStrategy != null) {
            return configuredStrategy;
        }

        // Default strategy based on item count
        if (itemCount <= 1) {
            return ListFormatStrategy.SINGLE_LINE;
        } else if (itemCount <= 3) {
            return ListFormatStrategy.SINGLE_LINE;
        } else {
            return ListFormatStrategy.SMART_BREAK;
        }
    }
}