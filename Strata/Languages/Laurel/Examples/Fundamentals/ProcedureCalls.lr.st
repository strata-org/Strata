/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
-- body is transparant despite having mutation
val fooReassign = procedure(): int {
  var x = 0;
  x = x + 1;
  assert x == 1;
  x = x + 1;
  x
}

val fooSingleAssign = procedure(): int {
  var x = 0
  var x2 = x + 1;
  var x3 = x2 + 1;
  x3
}

val proof = procedure() {
  assert fooReassign() == fooSingleAssign(); -- passes
}

/-
Example SMT translation

(set-logic ALL)

(define-fun fooReassign () Int
  (let ((x0 0))                    ; var x = 0
  (let ((x1 (+ x0 1)))             ; x = x + 1
  (let ((x2 (+ x1 1)))             ; x = x + 1
    x2)))))                        ; return x

(define-fun fooSingleAssign () Int
  (let ((x 0))                     ; var x = 0
  (let ((x2 (+ x 1)))              ; var x2 = x + 1
  (let ((x3 (+ x2 1)))             ; var x3 = x2 + 1
    x3))))                         ; return x3

; Verification conditions
; For fooReassign, we need to prove the assertion holds
(assert (let ((x0 0))
        (let ((x1 (+ x0 1)))
          (= x1 1))))               ; WP: assert x == 1 must hold

; Proof that both functions are equivalent
(assert (not (= (fooReassign) (fooSingleAssign))))

(check-sat)  ; Should return 'unsat' (meaning they ARE equal)
(get-model)  ; No model exists when unsat

-/