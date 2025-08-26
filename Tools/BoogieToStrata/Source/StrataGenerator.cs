using Microsoft.Boogie;
using Type = Microsoft.Boogie.Type;

namespace BoogieToStrata;

internal class StrataConversionException(IToken tok, string s) : Exception {
    public string Msg { get; } = $"{tok.filename}({tok.line},{tok.col}): {s}";
}

public class FieldTypeCollector : ReadOnlyVisitor {
    private readonly HashSet<Type> _usedTypes = [];

    public IEnumerable<Type> UsedTypes => _usedTypes.AsEnumerable();

    public override CtorType VisitCtorType(CtorType node) {
        if (node.Decl.Name.Contains("field", StringComparison.CurrentCultureIgnoreCase) && node.Arguments.Count == 1) {
            _usedTypes.Add(node.Arguments[0]);
        }
        return base.VisitCtorType(node);
    }
}

public class StrataGenerator : ReadOnlyVisitor {
    private readonly Stack<string> _breakLabels = new();
    private readonly VCGenOptions _options;
    private readonly Program _program;
    private readonly Dictionary<Type, HashSet<string>> _uniqueConstants = new();
    private readonly List<string> _userAxiomNames = [];
    private readonly TokenTextWriter _writer;
    private int _breakLabelCount;
    private int _indentLevel;
    private TypeCtorDecl? _refTypeCtor;
    private TypeCtorDecl? _fieldTypeCtor;
    private TypeSynonymDecl? _heapTypeSyn;

    private StrataGenerator(VCGenOptions options, TokenTextWriter writer, Program program) {
        _options = options;
        _writer = writer;
        _program = program;
    }

    public static void EmitProgramAsStrata(VCGenOptions options, Program p, TokenTextWriter writer) {
        var generator = new StrataGenerator(options, writer, p);

        var fieldTypeCollector = new FieldTypeCollector();
        fieldTypeCollector.Visit(p);
        generator.EmitHeader();
        try {
            var allBlocks = p.Implementations.SelectMany(i => i.Blocks);
            var liveDeclarations =
                !options.Prune
                    ? p.TopLevelDeclarations
                    : Pruner.GetLiveDeclarations(options, p, allBlocks.ToList()).LiveDeclarations.ToList();

            generator.FindSpecialTypes();

            var typeConstructors = p.TopLevelDeclarations.OfType<TypeCtorDecl>().ToList();
            if (typeConstructors.Count != 0) {
                generator.WriteLine("// Type constructors");
                // Always include all type constructors
                typeConstructors.ForEach(tcd => generator.VisitTypeCtorDecl(tcd));
                generator.WriteLine();
            }

            var typeSynonyms = liveDeclarations
                .OfType<TypeSynonymDecl>()
                .OrderBy(s => s.Body.IsMap ? 1 : 0)
                .ToList();
            if (typeSynonyms.Count != 0) {
                generator.WriteLine("// Type synonyms");
                typeSynonyms.ForEach(tcd => generator.VisitTypeSynonymDecl(tcd));
                generator.WriteLine();
            }

            var constants = liveDeclarations.OfType<Constant>().ToList();
            if (constants.Count != 0) {
                generator.WriteLine("// Constants");
                constants.ForEach(c => generator.VisitConstant(c));
                generator.WriteLine();
            }

            generator.EmitHeapFunctions(fieldTypeCollector);

            var functions = liveDeclarations.OfType<Function>().ToList();
            if (functions.Count != 0) {
                generator.WriteLine("// Functions");
                functions.ForEach(f => generator.VisitFunction(f));
                generator.WriteLine();
            }

            if (generator._uniqueConstants.Keys.Count != 0) {
                generator.WriteLine("// Unique const axioms");
                generator.EmitUniqueConstAxioms();
                generator.WriteLine();
            }

            var axioms = liveDeclarations.OfType<Axiom>().ToList();
            if (axioms.Count != 0) {
                generator.WriteLine("// Axioms");
                axioms.ForEach(a => generator.VisitAxiom(a));
                generator.WriteLine();
            }

            var variables = liveDeclarations.OfType<GlobalVariable>().ToList();
            if (variables.Count != 0) {
                generator.WriteLine("// Variables");
                variables.ForEach(gv => generator.VisitGlobalVariable(gv));
                generator.WriteLine();
            }

            if (p.Procedures.Count() != 0) {
                generator.WriteLine("// Uninterpreted procedures");
                p.Procedures.ForEach(p => generator.VisitProcedure(p));
            }

            if (p.Implementations.Count() != 0) {
                generator.WriteLine("// Implementations");
                p.Implementations.ForEach(i => generator.VisitImplementation(i));
            }

            generator.EmitFooter();
        } catch (StrataConversionException e) {
            Console.Error.WriteLine();
            Console.Error.WriteLine($"Failed translation: {e.Msg}");
            Environment.Exit(1);
        }
    }

    private bool IsPolyFieldType(TypeVariable var, Type toCheck) {
        return toCheck is CtorType checkCtor &&
               checkCtor.Decl == _fieldTypeCtor &&
               checkCtor.Arguments.Count == 1 &&
               checkCtor.Arguments[0] is TypeVariable typeVar &&
               typeVar.Name == var.Name;
    }

    private void FindSpecialTypes() {
        var typeCtorDecls =_program.TopLevelDeclarations.OfType<TypeCtorDecl>().ToList();
        foreach (var typeCtor in typeCtorDecls) {
            if (typeCtor.Name.Contains("ref", StringComparison.CurrentCultureIgnoreCase) && typeCtor.Arity == 0) {
                _refTypeCtor = typeCtor;
            }
            if (typeCtor.Name.Contains("field", StringComparison.CurrentCultureIgnoreCase) && typeCtor.Arity == 1) {
                _fieldTypeCtor = typeCtor;
            }
        }

        var typeSynDecls =_program.TopLevelDeclarations.OfType<TypeSynonymDecl>().ToList();
        foreach (var typeSyn
                 in typeSynDecls) {
            if (!typeSyn.Name.Contains("heap", StringComparison.CurrentCultureIgnoreCase) ||
                typeSyn.Body is not MapType mapType ||
                mapType.TypeParameters.Count != 1) {
                continue;
            }

            var typeParam = mapType.TypeParameters[0];
            if (mapType.Arguments.Count == 1) {
                var refArg = mapType.Arguments[0];
                var isRef = refArg is CtorType ctorType && ctorType.Decl == _refTypeCtor;
                var secondMapFieldIndexed = mapType.Result is MapType secondMap &&
                                            secondMap.Arguments.Count == 1 &&
                                            IsPolyFieldType(typeParam, secondMap.Arguments[0]) &&
                                            secondMap.Result is TypeVariable typeVar &&
                                            typeVar.Name == typeParam.Name;
                if (isRef && secondMapFieldIndexed) {
                    _heapTypeSyn = typeSyn;
                }
            } else if (mapType.Arguments.Count == 2) {
                var refArg = mapType.Arguments[0];
                var fieldArg = mapType.Arguments[1];
                var isRef = refArg is CtorType refArgCtor && refArgCtor.Decl == _refTypeCtor;
                var isField = IsPolyFieldType(typeParam, fieldArg);
                var isResult = mapType.Result is TypeVariable typeVar && typeVar.Name == typeParam.Name;
                if (isRef && isField && isResult) {
                    _heapTypeSyn = typeSyn;
                }
            }
        }
    }

    private static string SanitizeNameForStrata(string name) {
        return name
            .Replace('@', '_')
            .Replace('.', '_')
            .Replace('#', '_')
            .Replace('^', '_')
            .Replace("$", "_");
    }

    private void AddUniqueConst(Type t, string name) {
        if (!_uniqueConstants.TryGetValue(t, out var value)) {
            value = new HashSet<string>();
            _uniqueConstants[t] = value;
        }

        value.Add(name);
    }

    private void EmitUniqueConstAxioms() {
        var i = 0;
        foreach (var kv in _uniqueConstants) {
            if (kv.Value.Count == 1) {
                continue;
            }

            var axiomName = $"unique{i}";
            _userAxiomNames.Add(axiomName);
            // TODO: uncomment these axioms once Strata.Boogie supports them
            WriteText($"// axiom {axiomName}: distinct ");
            WriteList(kv.Value);
            WriteLine(";");
            i++;
        }
    }

    private void EmitHeader() {
        WriteLine("program Boogie;");
        WriteLine("type StrataHeap;");
        WriteLine("type StrataRef;");
        WriteLine("type StrataField (t: Type);");
        WriteLine();
    }

    private void EmitHeapFunctionsForType(Type ty) {
        WriteLine($"// Select function for {ty}");
        WriteText($"function StrataHeapSelect_{ty}(h: StrataHeap, r: StrataRef, f: StrataField ");
        VisitType(ty);
        WriteText(") : ");
        VisitType(ty);
        WriteLine(";");
        WriteLine($"// Update function for {ty}");
        WriteLine($"function StrataHeapUpdate_{ty}(h: StrataHeap, r: StrataRef, f: StrataField ");
        VisitType(ty);
        WriteText(", v: ");
        VisitType(ty);
        WriteLine(") : StrataHeap;");
    }

    private void EmitHeapFunctions(FieldTypeCollector fieldTypeCollector) {
        if (!fieldTypeCollector.UsedTypes.Any()) {
            return;
        }
        WriteLine();
        foreach (var ty in fieldTypeCollector.UsedTypes) {
            if (ty is TypeVariable) {
                continue;
            }

            EmitHeapFunctionsForType(ty);
            if (ty is TypeSynonymAnnotation typeSynonymAnnotation) {
                EmitHeapFunctionsForType(typeSynonymAnnotation.ExpandedType);
            }
        }
    }

    private void EmitFooter() { }

    private void IncIndent() {
        _indentLevel++;
    }

    private void DecIndent() {
        _indentLevel--;
    }

    private void Indent(string? str = null) {
        _writer.Write(_indentLevel, str ?? "");
    }

    private void IndentLine(string? str = null) {
        Indent(str);
        WriteLine();
    }

    private void WriteLine() {
        _writer.WriteLine();
    }

    private void WriteText(string text) {
        _writer.WriteText(text);
    }

    private string Name(string name) {
        return SanitizeNameForStrata(name);
    }

    private void WriteLine(string text) {
        _writer.WriteLine(text);
    }

    private void EmitSeparated<T>(IEnumerable<T> elems, Action<T> action, string separator) {
        var started = false;
        foreach (var elem in elems) {
            if (started) {
                WriteText(separator);
            }

            action(elem);
            started = true;
        }
    }

    private void WriteList(IEnumerable<string> strings) {
        WriteText("[");
        WriteText(string.Join(", ", strings));
        WriteText("]");
    }

    private void VisitMapType(List<Type> args, Type result) {
        if (args.Count == 0) {
            throw new StrataConversionException(result.tok, "Internal: map type has no arguments");
        }

        WriteText("(Map ");
        VisitType(args[0]);
        WriteText(" ");
        if (args.Count == 1) {
            VisitType(result);
        } else {
            VisitMapType(args.Skip(1).ToList(), result);
        }

        WriteText(")");
    }

    private void EmitTypeParameters(List<TypeVariable>? typeParameters) {
        if (typeParameters is null || typeParameters.Count == 0) {
            return;
        }
        WriteText("<");
        EmitSeparated(typeParameters, tv => WriteText(Name(tv.Name)), ", ");
        WriteText(">");
    }

    private void EmitTypeCtor(string name, List<Type> arguments) {
        if (arguments.Count >= 1) {
            WriteText("(");
        }

        if (name == _refTypeCtor?.Name) {
            name = "StrataRef";
        } else if (name == _fieldTypeCtor?.Name) {
            name = "StrataField";
        } else if (name == _heapTypeSyn?.Name) {
            name = "StrataHeap";
        }

        WriteText(Name(name));
        foreach (var t in arguments) {
            WriteText(" ");
            VisitType(t);
        }

        if (arguments.Count >= 1) {
            WriteText(")");
        }
    }

    public override Type VisitType(Type node) {
        switch (node) {
            case MapType mapType:
                EmitTypeParameters(mapType.TypeParameters);
                VisitMapType(mapType.Arguments, mapType.Result);
                break;
            case CtorType ctorType when ctorType.IsDatatype():
                throw new StrataConversionException(node.tok, "Not yet implemented: datatypes");
            case CtorType ctorType:
                EmitTypeCtor(ctorType.Decl.Name, ctorType.Arguments);
                break;
            case TypeSynonymAnnotation typeSynonymAnnotation:
                EmitTypeCtor(typeSynonymAnnotation.Decl.Name, typeSynonymAnnotation.Arguments);
                break;
            case TypeVariable typeVariable:
                WriteText(Name(typeVariable.Name));
                break;
            case BvType bvType:
                WriteText($"bv{bvType.Bits}");
                break;
            case BasicType basicType:
                if (basicType.IsBool) {
                    WriteText("bool");
                } else if (basicType.IsInt) {
                    WriteText("int");
                } else if (basicType.IsString) {
                    WriteText("string");
                } else if (basicType.IsReal) {
                    WriteText("real");
                } else if (basicType.IsBv) {
                    WriteText($"bv{basicType.BvBits}");
                } else {
                    throw new StrataConversionException(node.tok, $"Unknown basic type: {node.GetType()}");
                }

                break;
            default:
                throw new StrataConversionException(node.tok, $"Unknown type: {node.GetType()}");
        }

        return node;
    }

    public override Trigger? VisitTrigger(Trigger trigger) {
        while (trigger != null) {
            WriteText("{");
            EmitSeparated(trigger.Tr, e => VisitExpr(e), ", ");
            WriteText("} ");
            trigger = trigger.Next;
        }

        return trigger;
    }

    private bool ValidHeapArgs(Expr? heapExpr, Expr? refExpr, Expr? fieldExpr) {
        if (heapExpr is null || refExpr is null) {
            return false;
        }
        var heapTypeMatches = heapExpr.Type is TypeSynonymAnnotation typeSyn && typeSyn.Decl == _heapTypeSyn;
        var refTypeMatches = refExpr.Type.IsCtor && refExpr.Type.AsCtor?.Decl.Name == _refTypeCtor?.Name;
        var fieldTypeMatches = fieldExpr == null || fieldExpr.Type.IsCtor && fieldExpr.Type.AsCtor?.Decl.Name == _fieldTypeCtor?.Name;
        return heapTypeMatches && refTypeMatches && fieldTypeMatches;
    }

    private void EmitHeapCall(string function, IEnumerable<Expr> args) {
        WriteText($"{function}(");
        EmitSeparated(args, e => VisitExpr(e), ", ");
        WriteText(")");
    }

    private bool EmitHeapOperation(NAryExpr expr, bool isUpdate) {
        Expr? heapExpr = null;
        Expr? refExpr = null;
        Expr? fieldExpr = null;
        Expr? valueExpr = null;
        var shortCount = isUpdate ? 3 : 2;
        var longCount = isUpdate ? 4 : 3;

        if (expr.Args.Count == shortCount && expr.Fun is MapSelect outerSelect &&
            expr.Args[0] is NAryExpr { Fun: MapSelect innerSelect } innerSelectExpr) {
            if (expr.Args.Count != 2 | innerSelectExpr.Args.Count != 2) {
                return false;
            }

            heapExpr = innerSelectExpr.Args[0];
            refExpr = innerSelectExpr.Args[1];
            fieldExpr = expr.Args[1];
        } else if (expr.Args.Count == shortCount && expr.Fun is MapStore outerStore &&
                   expr.Args[2] is NAryExpr { Fun: MapStore innerStore } innerStoreExpr) {
            heapExpr = expr.Args[0];
            refExpr = expr.Args[1];
            fieldExpr = innerStoreExpr.Args[1];
            valueExpr = innerStoreExpr.Args[2];
        } else if (expr.Args.Count == longCount) {
            heapExpr = expr.Args[0];
            refExpr = expr.Args[1];
            fieldExpr = expr.Args[2];
            valueExpr = isUpdate ? expr.Args[3] : null;
        }

        if (heapExpr is null || refExpr is null || fieldExpr is null) {
            return false;
        }

        if (!ValidHeapArgs(heapExpr, refExpr, fieldExpr)) {
            return false;
        }

        if (isUpdate && valueExpr is not null) {
            var tyStr = valueExpr.Type.ToString();
            EmitHeapCall($"StrataHeapUpdate_{tyStr}", [heapExpr, refExpr, fieldExpr, valueExpr]);
        } else {
            var tyStr = expr.Type.ToString();
            EmitHeapCall($"StrataHeapSelect_{tyStr}", [heapExpr, refExpr, fieldExpr]);
        }
        return true;
    }

    public override Expr VisitExpr(Expr node) {
        switch (node) {
            case LiteralExpr { isBigNum: true } literalExpr:
                WriteText(literalExpr.asBigNum.ToString());
                break;
            case LiteralExpr { isBool: true } literalExpr:
                WriteText(literalExpr.asBool ? "true" : "false");
                break;
            case LiteralExpr { isBvConst: true } literalExpr:
                WriteText($"bv{{{literalExpr.asBvConst.Bits}}}({literalExpr.asBvConst.Value})");
                break;
            case LiteralExpr { isBigDec: true } literalExpr:
                WriteText(literalExpr.asBigDec.ToString());
                break;
            case LiteralExpr { isString: true } literalExpr:
                // Escape the string properly
                WriteText($"\"{literalExpr.asString.Replace("\"", "\\\"")}\"");
                break;
            case LiteralExpr literalExpr:
                throw new StrataConversionException(node.tok, $"Unsupported literal type: {literalExpr}");
            case IdentifierExpr identifierExpr:
                WriteText(Name(identifierExpr.Name));
                break;
            case NAryExpr nAryExpr: {
                var fun = nAryExpr.Fun;
                var args = nAryExpr.Args;

                switch (fun) {
                    case BinaryOperator binaryOp: {
                        switch (binaryOp.Op) {
                            // Special handling for implication and equivalence
                            case BinaryOperator.Opcode.Imp:
                                WriteText("(");
                                VisitExpr(args[0]);
                                WriteText(" ==> ");
                                VisitExpr(args[1]);
                                WriteText(")");
                                break;
                            case BinaryOperator.Opcode.Iff:
                                WriteText("(");
                                VisitExpr(args[0]);
                                WriteText(" <==> ");
                                VisitExpr(args[1]);
                                WriteText(")");
                                break;
                            default:
                                var opSymbol = GetBinaryOperatorSymbol(node.tok, binaryOp);
                                WriteText("(");
                                VisitExpr(args[0]);
                                WriteText($" {opSymbol} ");
                                VisitExpr(args[1]);
                                WriteText(")");
                                break;
                        }

                        break;
                    }
                    case UnaryOperator unaryOp: {
                        var opSymbol = GetUnaryOperatorSymbol(node.tok, unaryOp);
                        WriteText($"{opSymbol}(");
                        VisitExpr(args[0]);
                        WriteText(")");
                        break;
                    }
                    case MapSelect: {
                        if (!EmitHeapOperation(nAryExpr, false)) {
                            VisitExpr(args[0]);
                            WriteText("[");
                            EmitSeparated(args.Skip(1), e => VisitExpr(e), "][");
                            WriteText("]");
                        }

                        break;
                    }
                    case MapStore:
                        var emittedHeapOperation = EmitHeapOperation(nAryExpr, true);
                        if (args.Count == 3 && !emittedHeapOperation) {
                            WriteText("(");
                            VisitExpr(args[0]);
                            WriteText("[");
                            VisitExpr(args[1]);
                            WriteText(" := ");
                            VisitExpr(args[2]);
                            WriteText("])");
                        } else if (args.Count == 4 && !emittedHeapOperation) {
                            var map = args[0];
                            var idx1 = args[1];
                            var idx2 = args[2];
                            var rhs = args[3];
                            WriteText("(");
                            VisitExpr(map);
                            WriteText("[");
                            VisitExpr(idx1);
                            WriteText(" := ");
                            VisitExpr(map);
                            WriteText("[");
                            VisitExpr(idx1);
                            WriteText("][");
                            VisitExpr(idx2);
                            WriteText(" := ");
                            VisitExpr(rhs);
                            WriteText("]])");
                        } else if (!emittedHeapOperation) {
                            throw new StrataConversionException(node.tok,
                                $"Unsupported map store argument count: {args.Count}");
                        }

                        break;
                    case FunctionCall functionCall: {
                        WriteText($"{Name(functionCall.FunctionName)}(");
                        EmitSeparated(args, e => VisitExpr(e), ", ");
                        WriteText(")");
                        break;
                    }
                    case IfThenElse:
                        WriteText("(if ");
                        VisitExpr(args[0]);
                        WriteText(" then ");
                        VisitExpr(args[1]);
                        WriteText(" else ");
                        VisitExpr(args[2]);
                        WriteText(")");
                        break;
                    case TypeCoercion:
                        VisitExpr(args[0]);
                        break;
                    default:
                        throw new StrataConversionException(node.tok, $"Unsupported function in NAryExpr: {fun}");
                }

                break;
            }
            case BvConcatExpr bvConcatExpr: {
                var e0 = bvConcatExpr.E0;
                var e1 = bvConcatExpr.E1;
                var e0size = e0.Type.BvBits;
                var e1size = e1.Type.BvBits;
                var rsize = bvConcatExpr.Type.BvBits;
                WriteText($"bvconcat{{{e0size}}}{{{e1size}}}(");
                VisitExpr(e0);
                WriteText(", ");
                VisitExpr(e1);
                WriteText(")");
                break;
            }
            case BvExtractExpr bvExtractExpr: {
                WriteText($"bvextract{{{bvExtractExpr.End}}}{{{bvExtractExpr.Start}}}(");
                VisitExpr(bvExtractExpr.Bitvector);
                WriteText(")");
                break;
            }
            case OldExpr oldExpr:
                WriteText("old(");
                VisitExpr(oldExpr.Expr);
                WriteText(")");
                break;
            case QuantifierExpr quantifierExpr: {
                var quantifier = quantifierExpr.Kind switch {
                    BinderKind.Forall => "forall",
                    BinderKind.Exists => "exists",
                    _ => throw new StrataConversionException(node.tok,
                        $"Unsupported quantifier kind: {quantifierExpr.Kind}")
                };
                WriteText($"({quantifier} ");
                EmitQuantifierVariables(quantifierExpr.Dummies);
                WriteText(" :: ");
                VisitTrigger(quantifierExpr.Triggers);
                if (quantifierExpr.Attributes != null) {
                    VisitQKeyValue(quantifierExpr.Attributes);
                    WriteText(" ");
                }

                VisitExpr(quantifierExpr.Body);
                WriteText(")");
                break;
            }
            case LambdaExpr lambdaExpr: {
                WriteText("(lambda ");
                EmitQuantifierVariables(lambdaExpr.Dummies);
                WriteText(" :: ");
                if (lambdaExpr.Attributes != null) {
                    VisitQKeyValue(lambdaExpr.Attributes);
                    WriteText(" ");
                }

                VisitExpr(lambdaExpr.Body);
                WriteText(")");
                break;
            }
            case LetExpr letExpr: {
                WriteText("(let ");
                for (var i = 0; i < letExpr.Dummies.Count; i++) {
                    if (i > 0) {
                        WriteText(", ");
                    }

                    WriteText(Name(letExpr.Dummies[i].Name));
                    WriteText(" := ");
                    VisitExpr(letExpr.Rhss[i]);
                }

                WriteText(" :: ");
                VisitExpr(letExpr.Body);
                WriteText(")");
                break;
            }
            default:
                throw new StrataConversionException(node.tok, $"Unsupported expression type: {node.GetType().Name}");
        }

        return node;
    }

    private string GetBinaryOperatorSymbol(IToken tok, BinaryOperator op) {
        return op.Op switch {
            BinaryOperator.Opcode.Add => "+",
            BinaryOperator.Opcode.Sub => "-",
            BinaryOperator.Opcode.Mul => "*",
            BinaryOperator.Opcode.Div => "div",
            BinaryOperator.Opcode.Mod => "mod",
            BinaryOperator.Opcode.Eq => "==",
            BinaryOperator.Opcode.Neq => "!=",
            BinaryOperator.Opcode.Lt => "<",
            BinaryOperator.Opcode.Le => "<=",
            BinaryOperator.Opcode.Gt => ">",
            BinaryOperator.Opcode.Ge => ">=",
            BinaryOperator.Opcode.And => "&&",
            BinaryOperator.Opcode.Or => "||",
            BinaryOperator.Opcode.Imp => "==>",
            BinaryOperator.Opcode.Iff => "<==>",
            BinaryOperator.Opcode.RealDiv => "/",
            BinaryOperator.Opcode.FloatDiv => "/",
            BinaryOperator.Opcode.Pow => "^",
            _ => throw new StrataConversionException(tok, "Unsupported operator: {op}")
        };
    }

    private string GetUnaryOperatorSymbol(IToken tok, UnaryOperator op) {
        return op.Op switch {
            UnaryOperator.Opcode.Not => "!",
            UnaryOperator.Opcode.Neg => "-",
            _ => throw new StrataConversionException(tok, "Unsupported operator: {op}")
        };
    }

    private void EmitQuantifierVariables(List<Variable> variables) {
        for (var i = 0; i < variables.Count; i++) {
            if (i > 0) {
                WriteText(", ");
            }

            WriteText(Name(variables[i].Name));
            WriteText(": ");
            VisitType(variables[i].TypedIdent.Type);
        }
    }

    public override Variable VisitVariable(Variable node) {
        WriteText(Name(node.Name));
        return node;
    }


    public override IList<Expr> VisitExprSeq(IList<Expr> exprSeq) {
        EmitSeparated(exprSeq, e => VisitExpr(e), ", ");
        return exprSeq;
    }

    public override Cmd VisitAssertCmd(AssertCmd node) {
        Indent("assert ");
        VisitExpr(node.Expr);
        WriteLine(";");
        return node;
    }

    public override Cmd VisitAssumeCmd(AssumeCmd node) {
        Indent("assume ");
        VisitExpr(node.Expr);
        WriteLine(";");
        return node;
    }

    public override Cmd VisitAssertEnsuresCmd(AssertEnsuresCmd node) {
        Indent("assert ");
        VisitExpr(node.Expr);
        WriteLine(";");
        return node;
    }

    public override Cmd VisitAssertRequiresCmd(AssertRequiresCmd node) {
        Indent("assert ");
        VisitExpr(node.Expr);
        WriteLine(";");
        return node;
    }

    private bool OppositeExprs(Expr e1, Expr e2) {
        var c1 =
            e1 is NAryExpr { Fun: UnaryOperator { Op: UnaryOperator.Opcode.Not } } e1Expr &&
            e1Expr.Args[0].ToString().Equals(e2.ToString());
        var c2 =
            e2 is NAryExpr { Fun: UnaryOperator { Op: UnaryOperator.Opcode.Not } } e2Expr &&
            e2Expr.Args[0].ToString().Equals(e1.ToString());
        var c3 =
            e1 is NAryExpr { Fun: BinaryOperator { Op: BinaryOperator.Opcode.Eq } } e1EqExpr &&
            e2 is NAryExpr { Fun: BinaryOperator { Op: BinaryOperator.Opcode.Neq } } e2NeqExpr &&
            e1EqExpr.Args[0].ToString().Equals(e2NeqExpr.Args[0].ToString()) &&
            e1EqExpr.Args[1].ToString().Equals(e2NeqExpr.Args[1].ToString());
        var c4 =
            e1 is NAryExpr { Fun: BinaryOperator { Op: BinaryOperator.Opcode.Neq } } e1NeqExpr &&
            e2 is NAryExpr { Fun: BinaryOperator { Op: BinaryOperator.Opcode.Eq } } e2EqExpr &&
            e1NeqExpr.Args[0].ToString().Equals(e2EqExpr.Args[0].ToString()) &&
            e1NeqExpr.Args[1].ToString().Equals(e2EqExpr.Args[1].ToString());
        return c1 || c2 || c3 || c4;
    }

    private Expr? OppositeBlockCondition(Block b1, Block b2) {
        if (b1.Cmds.First() is AssumeCmd c1 && b2.Cmds.First() is AssumeCmd c2) {
            return OppositeExprs(c1.Expr, c2.Expr) ? c1.Expr : null;
        } else {
            return null;
        }
    }

    public override GotoCmd VisitGotoCmd(GotoCmd node) {
        if (node.LabelTargets.Count == 1) {
            IndentLine($"goto {Name(node.LabelTargets[0].Label)};");
        } else if (node.LabelTargets.Count == 2) {
            var thenBlock = node.LabelTargets[0];
            var elseBlock = node.LabelTargets[1];
            var cond = OppositeBlockCondition(thenBlock, elseBlock);
            if (cond != null) {
                Indent("if (");
                VisitExpr(cond);
                WriteLine($") {{ goto {Name(thenBlock.Label)}; }} else {{ goto {Name(elseBlock.Label)}; }}");
            } else {
                throw new StrataConversionException(node.tok, "Unsupported: goto with two targets that aren't obvious inverses");
            }

        } else {
            throw new StrataConversionException(node.tok, "Unsupported: goto with multiple targets");
        }

        return node;
    }

    private void EmitSimpleAssign(SimpleAssignLhs lhs, Expr rhs) {
        Indent();
        WriteText($"{Name(lhs.AssignedVariable.Name)} := ");
        VisitExpr(rhs);
        WriteLine(";");
    }

    public override Cmd VisitAssignCmd(AssignCmd node) {
        //Indent("// ");
        //node.Emit(_writer, 0);
        //WriteLine();
        foreach (var (l, r) in node.Lhss.Zip(node.Rhss)) {
            if (l is MapAssignLhs _) {
                VisitAssignCmd(node.AsSimpleAssignCmd);
                break;
            }

            if (l is SimpleAssignLhs simpleAssignLhs) {
                EmitSimpleAssign(simpleAssignLhs, r);
            } else {
                throw new StrataConversionException(node.tok, $"Unsupported assignment lhs: {l}");
            }
        }

        return node;
    }

    public override ReturnCmd VisitReturnCmd(ReturnCmd node) {
        IndentLine("goto end;");
        return node;
    }

    public override Cmd VisitCallCmd(CallCmd node) {
        var p = node.callee;
        Indent("call ");
        if (node.Outs.Count > 0) {
            EmitSeparated(node.Outs, e => VisitExpr(e), ", ");
            WriteText(" := ");
        }

        WriteText($"{Name(p)}(");
        EmitSeparated(node.Ins, e => VisitExpr(e), ", ");
        WriteLine(");");
        // TODO: assume where expressions on all modified variables, all output variables
        return node;
    }

    public override Cmd VisitHavocCmd(HavocCmd node) {
        foreach (var x in node.Vars) {
            IndentLine($"havoc {Name(x.Name)};");
            EmitWhereAssumption(x.Decl.TypedIdent);
        }

        return node;
    }

    public override ReturnExprCmd VisitReturnExprCmd(ReturnExprCmd node) {
        throw new StrataConversionException(node.tok, "Unsupported: return expression command");
    }

    public override Cmd VisitCommentCmd(CommentCmd node) {
        Indent($"// {node.Comment}");
        return node;
    }

    private void EmitIfCmd(IfCmd ifCmd) {
        WriteText("if (");
        if (ifCmd.Guard != null) {
            VisitExpr(ifCmd.Guard);
        } else {
            WriteText("*");
        }

        WriteLine(") {");
        IncIndent();
        EmitStmtList(ifCmd.Thn);
        DecIndent();
        IndentLine("}");
        if (ifCmd.ElseIf != null) {
            Indent("else ");
            EmitIfCmd(ifCmd.ElseIf);
        }

        if (ifCmd.ElseBlock != null) {
            IndentLine("else {");
            IncIndent();
            EmitStmtList(ifCmd.ElseBlock);
            DecIndent();
            IndentLine("}");
        }
    }

    private void EmitWhileCmd(WhileCmd whileCmd) {
        var label = $"break_{_breakLabelCount++}";
        _breakLabels.Push(label);
        WriteText("while (");
        if (whileCmd.Guard != null) {
            VisitExpr(whileCmd.Guard);
        } else {
            WriteText("*");
        }

        WriteLine(")");
        if (whileCmd.Invariants.Count != 0) {
            IncIndent();
            Indent("invariant");
            EmitSeparated(whileCmd.Invariants, i => VisitExpr(i.Expr), " && ");
            WriteLine(";");
            DecIndent();
        }
        IndentLine("{");
        IncIndent();
        EmitStmtList(whileCmd.Body);
        DecIndent();
        IndentLine("}");
        IndentLine($"{label}: {{}}");
        _breakLabels.Pop();
    }

    private void EmitStructuredCmd(StructuredCmd cmd) {
        if (cmd is IfCmd ifCmd) {
            Indent();
            EmitIfCmd(ifCmd);
        } else if (cmd is WhileCmd whileCmd) {
            Indent();
            EmitWhileCmd(whileCmd);
        } else if (cmd is BreakCmd breakCmd) {
            Indent();
            if (breakCmd.Label != null) {
                IndentLine($"goto {Name(breakCmd.Label)};");
            } else if (_breakLabels.TryPeek(out var label)) {
                IndentLine($"goto {label};");
            } else {
                throw new StrataConversionException(cmd.tok, "Internal: break statement outside loop");
            }
        } else {
            throw new StrataConversionException(cmd.tok, $"Unsupported structured command: {cmd}");
        }
    }

    private void EmitBigBlock(BigBlock bigBlock) {
        if (bigBlock.LabelName != null) {
            IndentLine($"{Name(bigBlock.LabelName)}: {{");
            IncIndent();
        }

        foreach (var simpleCmd in bigBlock.simpleCmds) {
            Visit(simpleCmd);
        }

        if (bigBlock.ec != null) {
            EmitStructuredCmd(bigBlock.ec);
        } else if (bigBlock.tc != null) {
            Visit(bigBlock.tc);
        }

        if (bigBlock.LabelName != null) {
            DecIndent();
            IndentLine("}");
        }
    }

    private void EmitStmtList(StmtList stmtList) {
        // TODO: cross-platform newline?
        EmitSeparated(stmtList.BigBlocks, EmitBigBlock, "\n");
    }

    public override Block VisitBlock(Block node) {
        var label = BlockName(node);
        IndentLine($"{label}: {{");
        IncIndent();
        node.Cmds.ForEach(c => Visit(c));
        if (node.TransferCmd is ReturnCmd returnCmd) {
            VisitReturnCmd(returnCmd);
        } else if (node.TransferCmd is ReturnExprCmd returnExprCmd) {
            VisitReturnExprCmd(returnExprCmd);
        } else if (node.TransferCmd is GotoCmd gotoCmd) {
            VisitGotoCmd(gotoCmd);
        } else {
            throw new StrataConversionException(node.TransferCmd.tok,
                $"Unsupported transfer command: {node.TransferCmd}");
        }

        DecIndent();
        IndentLine("}}");
        return node;
    }

    public override Constant VisitConstant(Constant node) {
        var ti = node.TypedIdent;
        WriteText($"const {Name(ti.Name)} : ");
        VisitType(ti.Type);
        if (node.Unique) {
            AddUniqueConst(ti.Type, ti.Name);
        }

        WriteLine(";");
        return node;
    }

    public override GlobalVariable VisitGlobalVariable(GlobalVariable node) {
        var ti = node.TypedIdent;
        WriteText($"var {Name(ti.Name)} : ");
        VisitType(ti.Type);
        WriteLine(";");
        return node;
    }

    public override Declaration VisitTypeCtorDecl(TypeCtorDecl node) {
        // Don't emit these special types if we've found them. They'll
        // be pre-declared.
        if (node == _refTypeCtor || node == _fieldTypeCtor) {
            return node;
        }

        WriteText($"type {Name(node.Name)}");
        if (node.Arity > 0) {
            WriteText(" (");
        }
        for (var i = 0; i < node.Arity; ++i) {
            if (i > 0) {
                WriteText(", ");
            }
            WriteText($"t{i} : Type");
        }
        if (node.Arity > 0) {
            WriteText(")");
        }

        WriteLine(";");
        return node;
    }

    public override Declaration VisitTypeSynonymDecl(TypeSynonymDecl node) {
        // Don't emit this special type if we've found it. It'll be
        // pre-declared.
        if (node == _heapTypeSyn) {
           return node;
        }

        WriteText($"type {Name(node.Name)}");
        if (node.TypeParameters.Count > 0) {
            WriteText(" (");
        }
        EmitSeparated(node.TypeParameters, tp => WriteText($"{Name(tp.Name)} : Type"), ", ");
        if (node.TypeParameters.Count > 0) {
            WriteText(")");
        }

        if (node.Body != null) {
            WriteText(" := ");
            VisitType(node.Body);
        }

        WriteLine(";");

        return node;
    }

    public override Axiom VisitAxiom(Axiom node) {
        var n = 0;
        var name = $"ax_l{node.tok.line}c{node.tok.col}";
        while (_userAxiomNames.Contains(name)) {
            name = $"ax_l{node.tok.line}c{node.tok.col}_{n}";
            n += 1;
        }

        WriteText($"axiom [{name}]: ");
        VisitExpr(node.Expr);
        WriteLine(";");
        _userAxiomNames.Add(name);
        return node;
    }

    private void EmitUnopBody(Function function, string op) {
        var sanitizedArgs =
            function.InParams.Select(i => SanitizeNameForStrata(i.Name)).ToArray();
        WriteLine($" {{ {op} {sanitizedArgs[0]} }}");
    }

    private void EmitBinopBody(Function function, string op) {
        var sanitizedArgs =
            function.InParams.Select(i => SanitizeNameForStrata(i.Name)).ToArray();
        WriteLine($" {{ {sanitizedArgs[0]} {op} {sanitizedArgs[1]} }}");
    }

    private void EmitCallBody(Function function, string fn) {
        var sanitizedArgs =
            function.InParams.Select(i => SanitizeNameForStrata(i.Name));
        var argStr = string.Join(", ", sanitizedArgs);
        WriteLine($" {{ {fn}({argStr}) }}");
    }

    // If the function has an SMT builtin attribute, emit a body
    // that calls that builtin.
    private void MaybeEmitBuiltinBody(Function function) {
        var builtinAttr = QKeyValue.FindStringAttribute(function.Attributes, "bvbuiltin");
        switch (builtinAttr) {
            case "bvneg": EmitUnopBody(function, "-"); break;
            case "bvadd": EmitBinopBody(function, "+"); break;
            case "bvsub": EmitBinopBody(function, "-"); break;
            case "bvmul": EmitBinopBody(function, "*"); break;
            case "bvsdiv": EmitBinopBody(function, "sdiv"); break;
            case "bvsrem": EmitBinopBody(function, "smod"); break;
            case "bvudiv": EmitBinopBody(function, "div"); break;
            case "bvurem": EmitBinopBody(function, "mod"); break;
            case "bvand": EmitBinopBody(function, "&"); break;
            case "bvor": EmitBinopBody(function, "|"); break;
            case "bvxor": EmitBinopBody(function, "^"); break;
            case "bvnot": EmitUnopBody(function, "~"); break;
            case "bvshl": EmitBinopBody(function, "<<"); break;
            case "bvlshr": EmitBinopBody(function, ">>"); break;
            case "bvashr": EmitBinopBody(function, ">>>"); break;
            case "bvslt": EmitBinopBody(function, "<s"); break;
            case "bvsle": EmitBinopBody(function, "<=s"); break;
            case "bvsgt": EmitBinopBody(function, ">s"); break;
            case "bvsge": EmitBinopBody(function, ">=s"); break;
            case "bvult": EmitBinopBody(function, "<"); break;
            case "bvule": EmitBinopBody(function, "<="); break;
            case "bvugt": EmitBinopBody(function, ">"); break;
            case "bvuge": EmitBinopBody(function, ">="); break;
            case "concat": EmitCallBody(function, "bvconcat"); break;
            case null: WriteLine(";"); break;
            default:
                if (builtinAttr.StartsWith("(_ extract ")) {
                    var words = builtinAttr.Split();
                    var hi = words[2];
                    var lo = words[3].Replace(")", "");
                    EmitCallBody(function, $"bvextract{{{hi}}}{{{lo}}}");
                } else {
                    WriteLine($"; // Unsupported builtin function {builtinAttr}");
                }
                break;
        }
    }

    public override Function VisitFunction(Function node) {
        WriteText($"function {Name(node.Name)}");
        EmitTypeParameters(node.TypeParameters);
        WriteText("(");
        WriteFormals(node.InParams);
        WriteText(") : (");
        // TODO: this isn't parseable by Strata if it has more than one element
        WriteVariableTypes(node.OutParams);
        WriteText(")");

        if (node.Body is null) {
            MaybeEmitBuiltinBody(node);
            return node;
        }

        WriteLine(" {");
        IncIndent();
        Indent();
        VisitExpr(node.Body);
        WriteLine();
        DecIndent();
        WriteLine("}");
        return node;
    }

    private string BlockName(Block b) {
        return Name(b.Label);
    }

    private bool UnsupportedQuantifier(Expr expr) {
        if (expr is QuantifierExpr quantifierExpr) {
            return quantifierExpr.TypeParameters.Any();
        }

        return false;
    }

    private void WriteProcedureHeader(Procedure proc) {
        WriteText($"procedure {Name(proc.Name)}");
        EmitTypeParameters(proc.TypeParameters);
        WriteText("(");
        WriteFormals(proc.InParams);
        WriteText(")");
        WriteText(" returns (");
        WriteFormals(proc.OutParams);
        WriteLine(")");

        if (proc.Modifies.Count != 0 || proc.Requires.Count != 0 || proc.Ensures.Count != 0) {
            WriteLine("spec {");
            IncIndent();
            foreach (var mod in proc.Modifies) {
                IndentLine($"modifies {Name(mod.Name)};");
            }

            foreach (var req in proc.Requires) {
                Indent();
                if (UnsupportedQuantifier(req.Condition)) {
                    WriteText("// ");
                }
                if (req.Free) {
                    WriteText("free ");
                }
                WriteText("requires ");
                VisitExpr(req.Condition);
                WriteLine(";");
            }

            foreach (var ens in proc.Ensures) {
                Indent();
                if (UnsupportedQuantifier(ens.Condition)) {
                    WriteText("// ");
                }
                if (ens.Free) {
                    WriteText("free ");
                }
                WriteText("ensures ");
                VisitExpr(ens.Condition);
                WriteLine(";");
            }

            DecIndent();
            WriteText("}");
        }
    }

    public override Procedure VisitProcedure(Procedure node) {
        if (!_program.Implementations.Any(i => i.Name.Equals(node.Name))) {
            WriteProcedureHeader(node);
            WriteLine(";");
            WriteLine();
        }

        return node;
    }

    private void WriteFormals(List<Variable> variables) {
        var n = 0;
        EmitSeparated(variables, v => {
            var name = v.TypedIdent.Name ?? "";
            if (name == "") {
                name = $"x{n++}";
            }

            WriteText($"{Name(name)} : ");
            VisitType(v.TypedIdent.Type);
        }, ", ");
    }

    private void WriteVariableTypes(List<Variable> variables) {
        EmitSeparated(variables, v => VisitType(v.TypedIdent.Type), ", ");
    }

    private void EmitWhereAssumption(TypedIdent typedIdent) {
        if (typedIdent.WhereExpr != null) {
            Indent("assume ");
            VisitExpr(typedIdent.WhereExpr);
            WriteLine(";");
        }
    }

    public override Implementation VisitImplementation(Implementation node) {
        WriteProcedureHeader(node.Proc);
        WriteLine();
        WriteLine("{");
        IncIndent();

        foreach (var v in node.InParams) {
            EmitWhereAssumption(v.TypedIdent);
        }

        foreach (var v in node.OutParams) {
            EmitWhereAssumption(v.TypedIdent);
        }

        foreach (var v in node.LocVars) {
            Indent($"var {Name(v.Name)} : ");
            VisitType(v.TypedIdent.Type);
            WriteLine(";");
            EmitWhereAssumption(v.TypedIdent);
        }

        if (node.StructuredStmts != null) {
            EmitStmtList(node.StructuredStmts);
        } else {
            foreach (var blk in node.Blocks) {
                VisitBlock(blk);
            }
        }

        IndentLine("end : {}");

        DecIndent();
        WriteLine("};");
        WriteLine();

        return node;
    }

    public override QKeyValue VisitQKeyValue(QKeyValue node) {
        // TODO: emit these once they can be parsed
        // node.Emit(_writer);
        return node;
    }

    public override Cmd VisitRevealCmd(HideRevealCmd node) {
        // Skip for now, but could be used to inform proof later.
        return node;
    }

    /* ==== Nodes that should never be visited directly ==== */

    public override Program VisitProgram(Program node) {
        throw new StrataConversionException(node.tok, "Internal: Program should never be directly visited.");
    }

    public override Declaration VisitDeclaration(Declaration node) {
        throw new StrataConversionException(node.tok, "Internal: Declaration should never be directly visited.");
    }

    public override DeclWithFormals VisitDeclWithFormals(DeclWithFormals node) {
        throw new StrataConversionException(node.tok, "Internal: DeclWithFormals should never be directly visited.");
    }

    public override List<Declaration> VisitDeclarationList(List<Declaration> declarationList) {
        throw new StrataConversionException(declarationList[0].tok,
            $"Internal: List<Declaration> should never be directly visited ({declarationList}).");
    }

    public override Requires VisitRequires(Requires requires) {
        throw new StrataConversionException(requires.tok, "Internal: Requires should never be directly visited.");
    }

    public override Ensures VisitEnsures(Ensures ensures) {
        throw new StrataConversionException(ensures.tok, "Internal: Ensures should never be directly visited.");
    }

    public override List<Requires> VisitRequiresSeq(List<Requires> requiresSeq) {
        throw new StrataConversionException(requiresSeq[0].tok,
            "Internal: List<Requires> should never be directly visited.");
    }

    public override List<Ensures> VisitEnsuresSeq(List<Ensures> ensuresSeq) {
        throw new StrataConversionException(ensuresSeq[0].tok,
            "Internal: List<Ensures> should never be directly visited.");
    }

    public override List<Block> VisitBlockSeq(List<Block> blockSeq) {
        throw new StrataConversionException(blockSeq[0].tok,
            $"Internal: List<Block> should never be directly visited ({blockSeq}).");
    }

    public override IList<Block> VisitBlockList(IList<Block> blocks) {
        throw new StrataConversionException(blocks[0].tok,
            $"Internal: List<Block> should never be directly visited ({blocks}).");
    }

    public override BoundVariable VisitBoundVariable(BoundVariable node) {
        throw new StrataConversionException(node.tok, "Internal: BoundVariable should never be directly visited.");
    }

    public override Formal VisitFormal(Formal node) {
        throw new StrataConversionException(node.tok, "Internal: Formal should never be directly visited.");
    }

    public override LocalVariable VisitLocalVariable(LocalVariable node) {
        throw new StrataConversionException(node.tok, "Internal error: LocalVariable should never be directly visited.");
    }

    public override Type VisitUnresolvedTypeIdentifier(UnresolvedTypeIdentifier node) {
        throw new StrataConversionException(node.tok, "Internal: UnresolvedTypeIdentifier should never appear.");
    }

    public override List<Variable> VisitVariableSeq(List<Variable> variableSeq) {
        throw new StrataConversionException(variableSeq[0].tok,
            $"Internal: List<Variable> should never be directly visited ({variableSeq}).");
    }

    public override HashSet<Variable> VisitVariableSet(HashSet<Variable> node) {
        throw new StrataConversionException(Token.NoToken,
            $"Internal: HashSet<Variable> should never be directly visited ({node}).");
    }

    public override AssignLhs VisitMapAssignLhs(MapAssignLhs node) {
        throw new StrataConversionException(node.tok, "Internal: MapAssignLhs should never be directly visited.");
    }

    public override AssignLhs VisitSimpleAssignLhs(SimpleAssignLhs node) {
        throw new StrataConversionException(node.tok, "Internal: SimpleAssignLhs should never be directly visited.");
    }

    /* ==== Unsupported nodes ==== */

    public override Expr VisitCodeExpr(CodeExpr node) {
        throw new StrataConversionException(node.tok, "Unsupported: CodeExpr");
    }

    public override ActionDeclRef VisitActionDeclRef(ActionDeclRef node) {
        throw new StrataConversionException(node.tok, "Unsupported: ActionDeclRef");
    }

    public override AssignLhs VisitFieldAssignLhs(FieldAssignLhs node) {
        throw new StrataConversionException(node.tok, "Unsupported: field assignment");
    }

    public override Cmd VisitUnpackCmd(UnpackCmd node) {
        throw new StrataConversionException(node.tok, "Unsupported: UnpackCmd.");
    }

    public override Cmd VisitParCallCmd(ParCallCmd node) {
        throw new StrataConversionException(node.tok, "Unsupported: ParCallCmd");
    }

    public override Cmd VisitStateCmd(StateCmd node) {
        throw new StrataConversionException(node.tok, "Unsupported: StateCmd");
    }

    public override List<CallCmd> VisitCallCmdSeq(List<CallCmd> callCmds) {
        throw new StrataConversionException(callCmds[0].tok, "Unsupported: List<CallCmd>");
    }

    public override Procedure VisitActionDecl(ActionDecl node) {
        throw new StrataConversionException(node.tok, "Unsupported: ActionDecl");
    }

    public override YieldingLoop VisitYieldingLoop(YieldingLoop node) {
        throw new StrataConversionException(node.YieldInvariants[0].tok, "Unsupported: YieldingLoop");
    }

    public override Dictionary<Block, YieldingLoop> VisitYieldingLoops(Dictionary<Block, YieldingLoop> node) {
        throw new StrataConversionException(Token.NoToken, "Unsupported: YieldingLoops");
    }

    public override Procedure VisitYieldProcedureDecl(YieldProcedureDecl node) {
        throw new StrataConversionException(node.tok, "Unsupported: YieldProcedureDecl");
    }

    public override Procedure VisitYieldInvariantDecl(YieldInvariantDecl node) {
        throw new StrataConversionException(node.tok, "Unsupported: YieldInvariantDecl");
    }

    public override Cmd VisitRE(RE node) {
        throw new StrataConversionException(node.tok, "Unsupported: RE");
    }

    public override List<RE> VisitRESeq(List<RE> reSeq) {
        throw new StrataConversionException(reSeq[0].tok, "Unsupported: List<RE>");
    }

    public override AtomicRE VisitAtomicRE(AtomicRE node) {
        throw new StrataConversionException(node.tok, "Unsupported: AtomicRE");
    }

    public override Choice VisitChoice(Choice node) {
        throw new StrataConversionException(node.tok, "Unsupported: Choice");
    }

    public override Sequential VisitSequential(Sequential node) {
        throw new StrataConversionException(node.tok, "Unsupported: Sequential");
    }

    /* ==== Nodes that should never appear in a resolved program ==== */

    public override Type VisitMapTypeProxy(MapTypeProxy node) {
        throw new StrataConversionException(node.tok,
            $"Internal: MapTypeProxy should never occur in resolved program ({node})");
    }

    public override Type VisitBvTypeProxy(BvTypeProxy node) {
        throw new StrataConversionException(node.tok,
            $"Internal: BvTypeProxy should never occur in resolved program ({node}).");
    }
}
