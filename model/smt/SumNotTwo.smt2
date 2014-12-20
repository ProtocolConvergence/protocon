
;(set-logic HORN)
(set-logic AUFLIA)
(set-info :smt-lib-version 2.0)

(declare-const M Int)
(assert (= M 3))
(declare-const N Int)
(assert (>= N 1))
(declare-const NSteps Int)
(assert (>= NSteps 0))

(define-fun act_P ((x_pd Int) (x Int) (x1 Int)) Bool
  (or
    (and (= x_pd 0) (= x 2) (= x1 0))
    (and (= x_pd 1) (= x 1) (= x1 2))
    (and (= x_pd 2) (= x 0) (= x1 1))
    ; Replace the above action with the one below to create a livelock.
    ;(and (= x_pd 2) (= x 0) (= x1 2))
    )
  )

(define-fun legit_P ((x_pd Int) (x Int)) Bool
  (not (= (+ x_pd x) 2)))

(define-fun dom_ck ((x Int)) Bool
  (and (>= x 0) (< x M)))

(define-fun idx_ck ((i Int)) Bool
  (and (>= i 0) (< i N)))

(define-fun step_ck ((t Int)) Bool
  (and (>= t 0) (< t NSteps)))

(define-fun dec1modN ((i Int)) Int
  ;(mod (- i 1) N))
  (ite (> i 0)
       (- i 1)
       (- N 1)))

;(declare-fun sigmap (Int Int) Int)
(declare-fun sigma (Int Int) Int)

;(define-fun sigma ((i Int) (t Int)) Int
;  (sigmap t i))

(assert
  (forall ((i Int) (t Int))
    (ite (and (idx_ck i) (or (step_ck t) (= t NSteps)))
         (dom_ck (sigma i t))
         (= (- 1) (sigma i t)))))

(assert
  (forall ((i Int) (t Int))
    ;; Use synchronous execution.
    (=> (and (idx_ck i) (step_ck t))
        (act_P (sigma (dec1modN i) t)
               (sigma i t)
               (sigma i (+ t 1))))
    ;; Use asynchronous execution.
    ;(=> (and (idx_ck i) (step_ck t)
    ;         (not (= (sigma i t) (sigma i (+ t 1)))))
    ;    (and
    ;      (act_P (sigma (dec1modN i) t)
    ;             (sigma i t)
    ;             (sigma i (+ t 1)))
    ;      (= (sigma (dec1modN i) t)
    ;         (sigma (dec1modN i) (+ t 1)))
    ;      ))
    ))

(assert
  (exists ((i Int))
    (not (= (sigma i 0) (sigma i 1)))))

(push)
(define-fun silent ((t Int)) Bool
  (forall ((i Int) (c1 Int))
    (=> (and (idx_ck i) (dom_ck c1))
        (not (act_P (sigma (dec1modN i) t) (sigma i t) c1)))))

(define-fun invariant ((t Int)) Bool
  (forall ((i Int))
    (=> (idx_ck i)
        (legit_P (sigma (dec1modN i) t) (sigma i t)))))

(push)
(echo "Checking for lying (silent) function, expect unsat.")
(assert (= NSteps 1))
(assert (silent 0))
(check-sat)
(pop)

(push)
(echo "Checking for bad transitions, expect unsat.")
(assert (invariant 0))
(assert (= NSteps 1))
;(assert (not (silent 0)))
(check-sat)
(pop)

(push)
(echo "Checking for deadlocks, expect unsat.")
(assert (not (invariant 0)))
(assert (silent 0))
(check-sat)
(pop)
(pop)


(push)
(echo "Checking for livelocks, expect unsat.")
(assert (> NSteps 0))
(assert
  (forall ((i Int))
    (=> (idx_ck i)
        (= (sigma i 0) (sigma i NSteps)))))


;(assert (= N 3))
;(assert (< N 8))
;(assert (= NSteps 8))


;(check-sat-using (then simplify solve-eqs))
;(check-sat-using (then normalize-bounds smt))
;(check-sat-using (then smt))
;(check-sat-using
;  (par-or
;    ;; Strategy 1: using seed 1
;    (using-params smt :random-seed 1)
;    ;; Strategy 1: using seed 2
;    (using-params smt :random-seed 2)
;    ;; Strategy 1: using seed 3
;    (using-params smt :random-seed 3)))

;(assert
;  (forall ((i Int) (t Int))
;    (=> (>= i N)
;        (= (- 1) (sigma i t)))))

;(assert
;  (forall ((i Int) (t Int))
;    (=> (> t NSteps)
;        (= (- 1) (sigma i t)))))

(check-sat)
;(check-sat-using (then horn smt))
(get-model)
(pop)


(exit)

; vim: ft=lisp:lw+=define-fun,forall,exists:
