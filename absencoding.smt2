; Scalar values
(declare-datatype S (
  (SInt (int-val Int))
  (SBool (bool-val Bool))
  (SString (string-val String))
  (SError)
))

; Value list (environment for de Bruijn indices)
(declare-datatype VList (
  (VNil)
  (VCons (head V) (tail VList))
))

; Expression AST
(declare-datatype E (
  (EConst (const-val S))
  (EBVar (bvar-idx Int))
  (EAbs (abs-body E))
  (EApp (app-fun E) (app-arg E))
  (EIte (ite-cond E) (ite-then E) (ite-else E))
  ; Simple operators
  (EEq (eq-left E) (eq-right E))
  (ELt (lt-left E) (lt-right E))
  ; Dictionary operations
  (EIn (in-key E) (in-dict E))  ; key membership check
))

; Value (result of evaluation)
(declare-datatype V (
  (VConst (vconst-val S))
  (VClosure (closure-env VList) (closure-body E))
  (VDict (dict-lookup V) (dict-has-key V))  ; lookup: key->value, has-key: key->bool
))

; Environment lookup
(declare-fun lookup (VList Int) V)

(assert (forall ((env VList) (idx Int))
  (= (lookup env idx)
     (ite (< idx 0)
          (VConst SError)
          (ite (= idx 0)
               (ite (is-VNil env)
                    (VConst SError)
                    (head env))
               (ite (is-VNil env)
                    (VConst SError)
                    (lookup (tail env) (- idx 1))))))))

; Relational evaluation semantics: "in environment env, expression e can evaluate to v"
(declare-fun canEval (VList E V) Bool)

; Constants always evaluate to themselves and ONLY to themselves
(assert (forall ((env VList) (s S)) 
  (canEval env (EConst s) (VConst s))))

(assert (forall ((env VList) (s S) (v V))
  (=> (canEval env (EConst s) v)
      (= v (VConst s)))))

; Bound variables look up in environment
(assert (forall ((env VList) (idx Int))
  (canEval env (EBVar idx) (lookup env idx))))

(assert (forall ((env VList) (idx Int) (v V))
  (=> (canEval env (EBVar idx) v)
      (= v (lookup env idx)))))

; Abstractions evaluate to closures capturing current environment
(assert (forall ((env VList) (body E)) 
  (canEval env (EAbs body) (VClosure env body))))

(assert (forall ((env VList) (body E) (v V))
  (=> (canEval env (EAbs body) v)
      (= v (VClosure env body)))))

; Conditionals: evaluate condition, then branch based on result
(assert (forall ((env VList) (cond E) (thenE E) (elseE E) (v V))
  (= (canEval env (EIte cond thenE elseE) v)
     (or
       ; If condition evaluates to true, result comes from then branch
       (exists ((vcond V))
         (and (canEval env cond vcond)
              (is-VConst vcond)
              (is-SBool (vconst-val vcond))
              (bool-val (vconst-val vcond))
              (canEval env thenE v)))
       ; If condition evaluates to false, result comes from else branch
       (exists ((vcond V))
         (and (canEval env cond vcond)
              (is-VConst vcond)
              (is-SBool (vconst-val vcond))
              (not (bool-val (vconst-val vcond)))
              (canEval env elseE v)))
       ; If condition evaluates to non-boolean, result is Error
       (exists ((vcond V))
         (and (canEval env cond vcond)
              (or (not (is-VConst vcond))
                  (not (is-SBool (vconst-val vcond))))
              (= v (VConst SError))))))))

; Equality: both operands must evaluate, then compare
(assert (forall ((env VList) (e1 E) (e2 E) (v V))
  (= (canEval env (EEq e1 e2) v)
     (or
       ; Integer equality
       (exists ((v1 V) (v2 V))
         (and (canEval env e1 v1) (canEval env e2 v2)
              (is-VConst v1) (is-VConst v2)
              (is-SInt (vconst-val v1)) (is-SInt (vconst-val v2))
              (= v (VConst (SBool (= (int-val (vconst-val v1)) (int-val (vconst-val v2))))))))
       ; String equality
       (exists ((v1 V) (v2 V))
         (and (canEval env e1 v1) (canEval env e2 v2)
              (is-VConst v1) (is-VConst v2)
              (is-SString (vconst-val v1)) (is-SString (vconst-val v2))
              (= v (VConst (SBool (= (string-val (vconst-val v1)) (string-val (vconst-val v2))))))))
       ; Type mismatch or non-const: Error
       (exists ((v1 V) (v2 V))
         (and (canEval env e1 v1) (canEval env e2 v2)
              (or (not (is-VConst v1))
                  (not (is-VConst v2))
                  (and (not (and (is-SInt (vconst-val v1)) (is-SInt (vconst-val v2))))
                       (not (and (is-SString (vconst-val v1)) (is-SString (vconst-val v2))))))
              (= v (VConst SError))))))))

; Less-than: both operands must be integers
(assert (forall ((env VList) (e1 E) (e2 E) (v V))
  (= (canEval env (ELt e1 e2) v)
     (or
       ; Both are integers: compare
       (exists ((v1 V) (v2 V))
         (and (canEval env e1 v1) (canEval env e2 v2)
              (is-VConst v1) (is-VConst v2)
              (is-SInt (vconst-val v1)) (is-SInt (vconst-val v2))
              (= v (VConst (SBool (< (int-val (vconst-val v1)) (int-val (vconst-val v2))))))))
       ; Type error: Error
       (exists ((v1 V) (v2 V))
         (and (canEval env e1 v1) (canEval env e2 v2)
              (or (not (is-VConst v1))
                  (not (is-VConst v2))
                  (not (is-SInt (vconst-val v1)))
                  (not (is-SInt (vconst-val v2))))
              (= v (VConst SError))))))))

; Application: function must be a closure or dict lookup, evaluate body with extended environment
(assert (forall ((env VList) (funE E) (argE E) (v V))
  (= (canEval env (EApp funE argE) v)
     (or
       ; Function is a closure: evaluate body with arg prepended to closure's environment
       (exists ((vfun V) (varg V))
         (and (canEval env funE vfun) (canEval env argE varg)
              (is-VClosure vfun)
              (canEval (VCons varg (closure-env vfun)) (closure-body vfun) v)))
       ; Function is a dict: apply the lookup closure
       (exists ((vfun V) (varg V))
         (and (canEval env funE vfun) (canEval env argE varg)
              (is-VDict vfun)
              (is-VClosure (dict-lookup vfun))
              (canEval (VCons varg (closure-env (dict-lookup vfun))) 
                       (closure-body (dict-lookup vfun)) v)))
       ; Function is neither closure nor dict: Error
       (exists ((vfun V) (varg V))
         (and (canEval env funE vfun) (canEval env argE varg)
              (not (is-VClosure vfun))
              (not (is-VDict vfun))
              (= v (VConst SError))))))))

; Membership check: key in dict
; A dictionary has a has-key closure that maps keys to booleans
(assert (forall ((env VList) (keyE E) (dictE E) (v V))
  (= (canEval env (EIn keyE dictE) v)
     (or
       ; Dict is a VDict: apply the has-key closure
       (exists ((vdict V) (vkey V))
         (and (canEval env dictE vdict) (canEval env keyE vkey)
              (is-VDict vdict)
              (is-VClosure (dict-has-key vdict))
              (canEval (VCons vkey (closure-env (dict-has-key vdict)))
                       (closure-body (dict-has-key vdict)) v)))
       ; Dict is not a VDict: Error
       (exists ((vdict V) (vkey V))
         (and (canEval env dictE vdict) (canEval env keyE vkey)
              (not (is-VDict vdict))
              (= v (VConst SError))))))))

; Encoding of the problem:
; var i;
; var r := { "x" => 1, "y" => 2 }
; assert i !in r || r[i] < 3

; Dictionary r is a VDict with two closures:
; 1. lookup: λkey. if key="x" then 1 else if key="y" then 2 else Error
; 2. has-key: λkey. if key="x" then true else if key="y" then true else false

(define-fun dict-r-lookup () E
  (EAbs 
    (EIte 
      (EEq (EBVar 0) (EConst (SString "x")))
      (EConst (SInt 1))
      (EIte
        (EEq (EBVar 0) (EConst (SString "y")))
        (EConst (SInt 2))
        (EConst SError)))))

(define-fun dict-r-has-key () E
  (EAbs
    (EIte
      (EEq (EBVar 0) (EConst (SString "x")))
      (EConst (SBool true))
      (EIte
        (EEq (EBVar 0) (EConst (SString "y")))
        (EConst (SBool true))
        (EConst (SBool false))))))

; We need to construct the VDict value directly in the assertion
; Since we can't directly construct values in expressions, we'll use a helper
(declare-const dict-r-val V)
(assert (= dict-r-val 
           (VDict (VClosure VNil dict-r-lookup) 
                  (VClosure VNil dict-r-has-key))))

; For the encoding, we need an expression that evaluates to this dict
; We'll use a constant that wraps it (extending our language slightly)
(declare-const dict-r-expr E)
(assert (canEval VNil dict-r-expr dict-r-val))

; Variable i (arbitrary string)
(declare-const i-val String)
(define-fun var-i () E (EConst (SString i-val)))

; i in r - membership check
(define-fun i-in-r () E (EIn var-i dict-r-expr))

; r[i] - dictionary lookup
(define-fun r-lookup () E (EApp dict-r-expr var-i))

; r[i] < 3
(define-fun r-i-lt-3 () E (ELt r-lookup (EConst (SInt 3))))

; The assertion: !(i in r) || r[i] < 3
; This must hold for ALL possible evaluation results in the empty environment
(assert 
  (forall ((in-result V) (lt-result V))
    (=>
      (and (canEval VNil i-in-r in-result) (canEval VNil r-i-lt-3 lt-result))
      (or
        ; i not in r (membership check returns false)
        (and (is-VConst in-result) 
             (is-SBool (vconst-val in-result)) 
             (not (bool-val (vconst-val in-result))))
        ; r[i] < 3 (comparison returns true)
        (and (is-VConst lt-result) 
             (is-SBool (vconst-val lt-result)) 
             (bool-val (vconst-val lt-result)))))))

(check-sat)
(get-model)
