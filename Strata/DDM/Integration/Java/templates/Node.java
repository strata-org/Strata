package com.strata.template;

public sealed interface Node {
    SourceRange sourceRange();
    java.lang.String operationName();
}
