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

    public IonValue serializeIdent(java.lang.String s) {
        IonSexp sexp = ion.newEmptySexp();
        sexp.add(ion.newSymbol("ident"));
        sexp.add(ion.newNull());
        sexp.add(ion.newString(s));
        return sexp;
    }

    public IonValue serializeStrlit(java.lang.String s) {
        IonSexp sexp = ion.newEmptySexp();
        sexp.add(ion.newSymbol("strlit"));
        sexp.add(ion.newNull());
        sexp.add(ion.newString(s));
        return sexp;
    }

    public IonValue serializeNum(java.math.BigInteger n) {
        IonSexp sexp = ion.newEmptySexp();
        sexp.add(ion.newSymbol("num"));
        sexp.add(ion.newNull());
        sexp.add(ion.newInt(n));
        return sexp;
    }

    public IonValue serializeDecimal(java.math.BigDecimal d) {
        IonSexp sexp = ion.newEmptySexp();
        sexp.add(ion.newSymbol("decimal"));
        sexp.add(ion.newNull());
        sexp.add(ion.newDecimal(d));
        return sexp;
    }

    public IonValue serializeBytes(byte[] bytes) {
        IonSexp sexp = ion.newEmptySexp();
        sexp.add(ion.newSymbol("bytes"));
        sexp.add(ion.newNull());
        sexp.add(ion.newBlob(bytes));
        return sexp;
    }

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
