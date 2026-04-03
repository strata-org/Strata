package com.strata.template;

import com.amazon.ion.IonSexp;

public sealed interface Node {
    SourceRange sourceRange();
    java.lang.String operationName();
    IonSexp toIon(IonSerializer $s);
}
