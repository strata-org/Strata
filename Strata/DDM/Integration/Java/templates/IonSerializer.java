package com.strata.template;

import com.amazon.ion.*;
import com.amazon.ion.system.*;

public class IonSerializer {
    private final IonSystem ion;

    public IonSerializer(IonSystem ion) {
        this.ion = ion;
    }

    /** Serialize a node as a top-level command (no "op" wrapper). */
    public IonValue serializeCommand(Node node) {
        return node.toIon(this);
    }

    /** Serialize a node as an argument (with "op" wrapper). */
    public IonValue serialize(Node node) {
        IonSexp sexp = ion.newEmptySexp();
        sexp.add(ion.newSymbol("op"));
        sexp.add(node.toIon(this));
        return sexp;
    }

    /** Create an s-expression with operation name and source range. */
    public IonSexp newOp(java.lang.String opName, SourceRange sr) {
        IonSexp sexp = ion.newEmptySexp();
        sexp.add(ion.newSymbol(opName));
        if (sr.start() == 0 && sr.stop() == 0) {
            sexp.add(ion.newNull());
        } else {
            IonSexp range = ion.newEmptySexp();
            range.add(ion.newInt(sr.start()));
            range.add(ion.newInt(sr.stop()));
            sexp.add(range);
        }
        return sexp;
    }

    private IonSexp newTagged(String symbol, IonValue value) {
        IonSexp sexp = ion.newEmptySexp();
        sexp.add(ion.newSymbol(symbol));
        sexp.add(ion.newNull());
        sexp.add(value);
        return sexp;
    }

    public IonValue serializeIdent(java.lang.String s) { return newTagged("ident", ion.newString(s)); }
    public IonValue serializeStrlit(java.lang.String s) { return newTagged("strlit", ion.newString(s)); }
    public IonValue serializeNum(java.math.BigInteger n) { return newTagged("num", ion.newInt(n)); }
    public IonValue serializeDecimal(java.math.BigDecimal d) { return newTagged("decimal", ion.newDecimal(d)); }
    public IonValue serializeBytes(byte[] bytes) { return newTagged("bytes", ion.newBlob(bytes)); }

    public IonValue serializeBool(boolean b) {
        IonSexp inner = ion.newEmptySexp();
        inner.add(ion.newSymbol(b ? "Init.boolTrue" : "Init.boolFalse"));
        inner.add(ion.newNull());
        IonSexp sexp = ion.newEmptySexp();
        sexp.add(ion.newSymbol("op"));
        sexp.add(inner);
        return sexp;
    }

    public <T> IonValue serializeOption(java.util.Optional<T> opt, java.util.function.Function<T, IonValue> f) {
        IonSexp sexp = ion.newEmptySexp();
        sexp.add(ion.newSymbol("option"));
        sexp.add(ion.newNull());
        opt.ifPresent(v -> sexp.add(f.apply(v)));
        return sexp;
    }

    public <T> IonValue serializeSeq(java.util.List<T> list, java.lang.String sepType, java.util.function.Function<T, IonValue> f) {
        IonSexp sexp = ion.newEmptySexp();
        sexp.add(ion.newSymbol(sepType));
        sexp.add(ion.newNull());
        for (T item : list) {
            sexp.add(f.apply(item));
        }
        return sexp;
    }
}
