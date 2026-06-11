package com.strata.template;

public record SourceRange(long start, long stop) {
    public static final SourceRange NONE = new SourceRange(0, 0);
}
