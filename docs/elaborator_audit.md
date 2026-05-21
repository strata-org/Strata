# Elaborator Full Audit

Every instance where the code deviates from the architecture.

## Catch-alls returning Any

1. **Line 80**: `instance : Inhabited FuncSig` — default has `returnType := .TCore "Any"`. Lean requires `Inhabited` but this default should never be used.

2. **Line 90**: `instance : Inhabited NameInfo` — default is `.variable (.TCore "Any")`. Same — Lean requirement, should never be reached.

3. **Line 219**: `eraseType` — `.TSet _ | .TMap _ _ | .Applied _ _ | .Intersection _ | .Unknown => .TCore "Any"`. These types shouldn't appear in well-typed Laurel from Translation. Should fail.

4. **Line 539**: `lookupProcOutputs` — `env.procGrades[callee]?.getD .pure`. Guesses `pure` if grade not found. Should fail.

5. **Line 553**: `lookupProcOutputs` — `| none => pure [("result", .TCore "Any")]`. Invents fake output if callee not found. Should fail.

6. **Line 594**: `synthValueVar` — `| some (.function sig) => pure (.var md id.text, eraseType sig.returnType)`. Functions shouldn't be referenced as values unless they're being called. Unclear if this is correct or a hack.

7. **Line 595**: `synthValueVar` — `| _ => pure (.var md id.text, .TCore "Any")`. Unknown name returns Any. Should fail.

8. **Line 626**: `synthValueFieldSelect` — `ft.getD (.TCore "Any")`. Field type lookup returned none. Should fail.

9. **Line 634**: `synthValueFieldSelect` — when `resolveFieldOwner` returns `none`, emits havoc with `Any`. Should fail (object type should tell us the class).

10. **Line 652**: `synthValueStaticCall` — `(← read).procGrades[callee.text]?.getD .pure`. Guesses pure if grade not found. Should fail.

11. **Line 659-661**: `synthValueStaticCall` — `| none => let checkedArgs ← args.mapM fun arg => checkValue arg (.TCore "Any"); pure (.staticCall md callee.text checkedArgs, .TCore "Any")`. Unknown callee returns Any. Should fail.

12. **Line 684-687**: `checkArgValues` — `| arg :: rest, [] => do let v ← checkValue arg (.TCore "Any")`. Extra args beyond params checked against Any. Should fail (arity mismatch).

13. **Line 861**: `elaborateCall` — `(← read).procGrades[callee.text]?.getD .pure`. Same as #4/#10. Guesses pure.

14. **Line 948-953**: `bindArgs` — `| arg :: restArgs, [] => ... (.TCore "Any")`. Extra args beyond params. Should fail.

## Option-returning lookups that should fail

15. **Line 400**: `lookupEnv` returns `Option NameInfo`. Should return `NameInfo` and fail if not found.

16. **Line 403-404**: `lookupFuncSig` returns `Option FuncSig`. Should return `FuncSig` and fail.

17. **Line 405-408**: `lookupFieldType` returns `Option HighType`. Should return `HighType` and fail.

## Structurally wrong

18. **Line 409-412**: `resolveFieldOwner` — global scan by field name instead of using the object's synthesized type.

19. **Line 910**: `checkProducer` `.Assign` multi-target — `| _ => checkProducers rest retTy grade`. Silently drops multi-target assignment. Should fail.

20. **Line 913**: `checkProducer` `.New` — `failure`. Should be implemented (at least for assignment context — bare new is pathological).

21. **Line 928-931**: `checkProducer` catch-all — emits havoc with `Any`. Should be `produce(checkValue stmt retTy)` for value expressions, `failure` for unsupported forms.

22. **Line 993**: `checkAssignFieldWrite` — `guard (Grade.leftResidual .heap grade |>.isSome)`. Grade check belongs in subgrading, not here.

## Missing from architecture

23. `checkProducer` is not total — no explicit cases for: `LiteralInt`, `LiteralBool`, `LiteralString`, `LiteralDecimal`, `Identifier`, `FieldSelect`, `PureFieldUpdate`, `PrimitiveOp`, `This`, `ReferenceEquals`, `AsType`, `IsType`, `Forall`, `Exists`, `Assigned`, `Old`, `Fresh`, `ProveBy`, `ContractOf`, `Return`, `InstanceCall`.

24. `checkProducerStaticCall` — no derivation tree previously (now fixed).

25. `checkAssignVar` — derivation exists but code was using `checkValue` (now fixed to `checkProducer`).

26. Doc `checkProducer` case list incomplete (now partially fixed but still references stale items).
