package com.strata.template;

import com.amazon.ion.*;
import com.amazon.ion.system.*;

public class IonSerializer {
    private final IonSystem ion;

    private static final java.util.Map<String, java.util.Map<String, String>> SEPARATORS = /*SEPARATOR_MAP*/;

    public IonSerializer(IonSystem ion) {
        this.ion = ion;
    }

    /** Serialize a node as a top-level command (no "op" wrapper). */
    public IonValue serializeCommand(Node node) {
        return serializeNode(node);
    }

    /** Serialize a node as an argument (with "op" wrapper). */
    public IonValue serialize(Node node) {
        return wrapOp(serializeNode(node));
    }

    private IonSexp serializeNode(Node node) {
        IonSexp sexp = ion.newEmptySexp();
        String opName = node.operationName();
        sexp.add(ion.newSymbol(opName));
        sexp.add(serializeSourceRange(node.sourceRange()));

        var fieldSeps = SEPARATORS.getOrDefault(opName, java.util.Map.of());
        for (var component : node.getClass().getRecordComponents()) {
            if (component.getName().equals("sourceRange")) continue;
            try {
                java.lang.Object value = component.getAccessor().invoke(node);
                String sep = fieldSeps.get(component.getName());
                sexp.add(serializeArg(value, sep, component.getType()));
            } catch (java.lang.Exception e) {
                throw new java.lang.RuntimeException("Failed to serialize " + component.getName(), e);
            }
        }
        return sexp;
    }

    private IonValue wrapOp(IonValue inner) {
        IonSexp sexp = ion.newEmptySexp();
        sexp.add(ion.newSymbol("op"));
        sexp.add(inner);
        return sexp;
    }

    private IonValue serializeSourceRange(SourceRange sr) {
        if (sr.start() == 0 && sr.stop() == 0) {
            return ion.newNull();
        }
        IonSexp sexp = ion.newEmptySexp();
        sexp.add(ion.newInt(sr.start()));
        sexp.add(ion.newInt(sr.stop()));
        return sexp;
    }

    private IonValue serializeArg(java.lang.Object value, String sep, java.lang.Class<?> type) {
        if (value == null) {
            return serializeOption(java.util.Optional.empty());
        }
        if (value instanceof Node n) {
            return serialize(n);
        }
        if (value instanceof java.lang.String s) {
            return serializeIdent(s);
        }
        if (value instanceof java.math.BigInteger bi) {
            return serializeNum(bi);
        }
        if (value instanceof java.math.BigDecimal bd) {
            return serializeDecimal(bd);
        }
        if (value instanceof byte[] bytes) {
            return serializeBytes(bytes);
        }
        if (value instanceof java.lang.Boolean b) {
            return serializeBool(b);
        }
        if (value instanceof java.util.Optional<?> opt) {
            return serializeOption(opt);
        }
        if (value instanceof java.util.List<?> list) {
            return serializeSeq(list, sep != null ? sep : "seq");
        }
        throw new java.lang.IllegalArgumentException("Unsupported type: " + type);
    }

    private IonValue serializeIdent(java.lang.String s) {
        IonSexp sexp = ion.newEmptySexp();
        sexp.add(ion.newSymbol("ident"));
        sexp.add(ion.newNull());
        sexp.add(ion.newString(s));
        return sexp;
    }

    private IonValue serializeNum(java.math.BigInteger n) {
        IonSexp sexp = ion.newEmptySexp();
        sexp.add(ion.newSymbol("num"));
        sexp.add(ion.newNull());
        sexp.add(ion.newInt(n));
        return sexp;
    }

    private IonValue serializeDecimal(java.math.BigDecimal d) {
        IonSexp sexp = ion.newEmptySexp();
        sexp.add(ion.newSymbol("decimal"));
        sexp.add(ion.newNull());
        sexp.add(ion.newDecimal(d));
        return sexp;
    }

    private IonValue serializeBytes(byte[] bytes) {
        IonSexp sexp = ion.newEmptySexp();
        sexp.add(ion.newSymbol("bytes"));
        sexp.add(ion.newNull());
        sexp.add(ion.newBlob(bytes));
        return sexp;
    }

    private IonValue serializeBool(boolean b) {
        IonSexp inner = ion.newEmptySexp();
        inner.add(ion.newSymbol(b ? "Init.boolTrue" : "Init.boolFalse"));
        inner.add(ion.newNull());
        return wrapOp(inner);
    }

    private IonValue serializeOption(java.util.Optional<?> opt) {
        IonSexp sexp = ion.newEmptySexp();
        sexp.add(ion.newSymbol("option"));
        sexp.add(ion.newNull());
        if (opt.isPresent()) {
            sexp.add(serializeArg(opt.get(), null, opt.get().getClass()));
        }
        return sexp;
    }

    private IonValue serializeSeq(java.util.List<?> list, String sepType) {
        IonSexp sexp = ion.newEmptySexp();
        sexp.add(ion.newSymbol(sepType));
        sexp.add(ion.newNull());
        for (java.lang.Object item : list) {
            sexp.add(serializeArg(item, null, item.getClass()));
        }
        return sexp;
    }
}
