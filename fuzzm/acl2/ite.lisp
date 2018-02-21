;; 
;; Copyright (C) 2017, Rockwell Collins
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;; 
;; 
(in-package "ACL2")
(include-book "coi/util/mv-nth" :dir :system)
;; -------------------------------------------------------------------
;;
;; A proof of the correctness of a more aggressive generalization
;; approach.  In this theory, we allow both expansion and contraction
;; of the generalized solution.  The 'alt' flag selects between the
;; two.  When alt is true, we are in the alternative universe where we
;; want to expand the state space around the solution.  When alt is
;; false, we return to our standard state space in which our only
;; option is to contract the state space around the solution.  The
;; transition from non-alt to alt takes place when we encounter an
;; 'and' expression with arguments that evaluate to differing values
;; under the solution.
;;
;; Our evaluator also includes 'ite' as a primitive construct.  While
;; ite rules might be derived from and/or, it is also possible that
;; they will allow certain optimizations that might otherwise remain
;; hidden.
;;
;; Note that our previous work did not consider whether or not the
;; generalization process had changed the expression.  This becomes
;; more important when considering 'ite' because, if the test
;; condition remains unchanged, it enables us to retain more of
;; the original structure.
;;
;; Correctness means:
;;
;; 1. Generalization preserves the polarity of the counterexample
;;
;; 2. Generalization preserves the polarity of any vector
;;    that differs from the counterexample
;;
;; Assuming that the counterexample falsifies the original expression,
;; this specification allows the generalizer to return a simpler
;; expression such that, if a vector falsifies the simpler expression,
;; it also falsifies the original expression.
;;
;; -------------------------------------------------------------------

;; -------------------------------------------------------------------
;;
;; Introduce the expression evaluator and related helper functions
;;
;; -------------------------------------------------------------------

(defun eval-expr (expr env)
  (case-match expr
    (('ite x y z)
     (let ((x (eval-expr x env))
           (y (eval-expr y env))
           (z (eval-expr z env)))
       (if x y z)))
    (('and x y)
     (let ((x (eval-expr x env))
           (y (eval-expr y env)))
       (and x y)))
    (('or x y)
     (let ((x (eval-expr x env))
           (y (eval-expr y env)))
       (or x y)))
    (('not x)
     (let ((x (eval-expr x env)))
       (not x)))
    (('id n)
     (nth n env))
    (& expr)))

(defun not-expr (expr)
  (case-match expr
    (('not x) x)
    (& `(not ,expr))))

(defun or-expr (x y)
  `(or ,x ,y))

(defun and-expr (x y)
  `(and ,x ,y))

(defun ite-expr (x y z)
  `(ite ,x ,y ,z))

(defthm commute-not-expr
  (iff (eval-expr (not-expr expr) env)
       (not (eval-expr expr env))))

(defthm commute-and-expr
  (iff (eval-expr (and-expr e1 e2) env)
       (and (eval-expr e1 env)
            (eval-expr e2 env))))

(defthm commute-or-expr
  (iff (eval-expr (or-expr e1 e2) env)
       (or (eval-expr e1 env)
           (eval-expr e2 env))))

(defthm commute-ite-expr
  (iff (eval-expr (ite-expr e1 e2 e3) env)
       (if (eval-expr e1 env)
           (eval-expr e2 env)
         (eval-expr e3 env))))

(in-theory (disable not-expr))
(in-theory (disable and-expr))
(in-theory (disable or-expr))
(in-theory (disable ite-expr))

(encapsulate
    (
     ((gen * * *) => *)
     )

  (local
   (defun gen (alt x cex)
     (declare (ignore alt cex))
     x))

  (defthm eval-expr-gen-idempotent
    (iff (eval-expr (gen alt expr cex) cex)
         (eval-expr expr cex)))
  
  (defthm gen-is-conservative
    (implies
     (iff (eval-expr expr any) (xor alt (not (eval-expr expr cex))))
     (iff (eval-expr (gen alt expr cex) any)
          (eval-expr expr any))))
  
  )

;; We can test out our cases here ..

(defstub gen-choice (alt x y z cex) nil)

(defstub foo (x) nil)

(defun gen-ite (alt x y z cex)
  (let ((xv (eval-expr x cex))
        (yv (eval-expr y cex))
        (zv (eval-expr z cex)))
    (cond
     ((and (not alt) (not xv) (not yv) (not zv))
      (let ((key (gen-choice alt x y z cex)))
        (let ((x- (gen alt x cex))
              (y- (gen alt y cex))
              (z- (gen alt z cex)))
          (case key
            (:_yz
             (or-expr y- z-))
            (:x_z
             (or-expr x- z-))
            (t
             (or-expr (and-expr x- y-) z-))))))
     ((and (not alt) xv (not yv) (not zv))
      (let ((key (gen-choice alt x y z cex)))
        (let ((x- (gen alt x cex))
              (x+ (gen (not alt) x cex))
              (y- (gen alt y cex))
              (z- (gen alt z cex)))
          (case key
            (:_yz
             (or-expr y- z-))
            (:xy_
             (or-expr (not-expr x-) y-))
            (:and
             (and-expr (or-expr x+ z-) (or-expr (not-expr x-) y-)))
            (:+xyz
             (or-expr (and-expr x+ y-) z-))
            (:ite
             (or-expr (and-expr x+ y-) (and-expr (not-expr x-) z-)))
            (t
             (or-expr y- (and-expr (not-expr x-) z-)))))))
     ((and alt xv (not yv) (not zv))
      (let ((key (gen-choice alt x y z cex)))
        (let ((x+ (gen alt x cex))
              (x- (gen (not alt) x cex))
              (y+ (gen alt y cex))
              (z+ (gen alt z cex)))
          (case key
            (:_yz
             (and-expr y+ z+))
            (:xy_
             (and-expr x- y+))
            (:x_z
             (and-expr (not-expr x+) z+))
            ;; Technically, any combination thereof ..
            (:ite
             (or-expr (and-expr x- y+) (and-expr (not-expr x+) z+)))
            (t
             (or-expr (and-expr x- y+) (and-expr (not-expr x+) z+)))))))
     (t
      (ite-expr x y z)))))

;;
;; Prove that the counterexample is unaffected by the generalization
;;
(defthm gen-ite-is-idempotent
  (iff (eval-expr (gen-ite alt x y z cex) cex)
       (eval-expr (ite-expr x y z) cex))
  :hints (("Goal" :do-not-induct t
           :do-not '(generalize eliminate-destructors))))

;;
;; Prove that the generalization is conservative
;;
(defthm gen-ite-is-conservative
  (implies
   (iff (eval-expr (ite-expr x y z) any)
        (xor alt (not (eval-expr (ite-expr x y z) cex))))
   (iff (eval-expr (gen-ite alt x y z cex) any)
        (eval-expr (ite-expr x y z) any)))
  :hints (("Goal" :do-not-induct t
           :do-not '(generalize eliminate-destructors))))

#|

(encapsulate
    (
     ((domain-restriction * * *) => *)
     )

  (local (defun domain-restriction (xexpr yexpr cex)
           (declare (ignore cex))
           (and-expr xexpr yexpr)))
  
  (defthm domain-restriction-captures-cex
    (implies
     (and
      (eval-expr xexpr cex)
      (eval-expr yexpr cex))
     (eval-expr (domain-restriction xexpr yexpr cex) cex)))

  ;; Please note that our specification for domain-restriction is
  ;; asymmetric.  The "kept" expression should be the first argument
  ;; and the "discarded" expression should be the second.
  (defthm domain-restriction-is-conservative-rewrite
    (implies
     (and
      (not (eval-expr yexpr any))
      (eval-expr xexpr any))
     (not (eval-expr (domain-restriction xexpr yexpr cex) any))))

  )

;; -------------------------------------------------------------------
;;
;; Characterize the behavior of the generalizer w/to "and".  This is
;; really the heart of our behavioral spec for the generalizer.
;;
;; -------------------------------------------------------------------

;; We use encapsulation to constrain the possible behaviors of
;; gen-and.  The gen-and-choice function is intended to reflect the
;; freedom we have in choosing behaviors for gen-and.
(encapsulate
 (
  ((gen-and * * * *) => *)
  ((gen-and-choice * * * *) => *)
  )

 (local 
  (defun gen-and-choice (alt xexpr yexpr cex) 
    (let ((xval (eval-expr xexpr cex))
          (yval (eval-expr yexpr cex)))
      (cond 
       (alt :both)
       (t
        (cond
         ((and xval yval)
          :both)
         (xval
          :right)
         (t
          :left)))))))

 (local 
  (defun gen-and (alt xexpr yexpr cex) 
    (let ((choice (gen-and-choice alt xexpr yexpr cex)))
      (cond
       ((equal choice :left)  xexpr)
       ((equal choice :right) yexpr)
       (t (and-expr xexpr yexpr))))))

 (defthm gen-and-options
   (equal (eval-expr (gen-and alt xexpr yexpr cex) env)
          (eval-expr (let ((choice (gen-and-choice alt xexpr yexpr cex)))
                       (let ((xval (eval-expr xexpr cex))
                             (yval (eval-expr yexpr cex)))
                         (cond
                          (alt
                           (if (and xval yval)
                               (cond
                                ((equal choice :left)  xexpr)
                                ((equal choice :right) yexpr)
                                (t                     (and-expr xexpr yexpr)))
                             (cond
                              ((equal choice :left)   (and-expr xexpr (domain-restriction xexpr yexpr cex)))
                              ((equal choice :right)  (and-expr (domain-restriction yexpr xexpr cex) yexpr))
                              (t                      (and-expr xexpr yexpr)))))
                          (t
                           (if xval
                               (if yval 
                                   (cond
                                    ((equal choice :left)  (and-expr xexpr (domain-restriction xexpr yexpr cex)))
                                    ((equal choice :right) (and-expr (domain-restriction yexpr xexpr cex) yexpr))
                                    (t (and-expr xexpr yexpr)))
                                 (cond
                                  ((equal choice :right) yexpr)
                                  (t (and-expr xexpr yexpr))))
                             (if yval 
                                 (cond
                                  ((equal choice :left) xexpr)
                                  (t (and-expr xexpr yexpr)))
                               (cond
                                ((equal choice :left)  xexpr)
                                ((equal choice :right) yexpr)
                                (t (and-expr xexpr yexpr))))))))) env)))
 
 )

;; -------------------------------------------------------------------
;;
;; The behavior of 'or' is simply the dual of 'and'
;;
;; -------------------------------------------------------------------

(defun gen-or (alt genx geny cex)
  (not-expr (gen-and alt (not-expr genx) (not-expr geny) cex)))

(defun gen-or-choice (alt xexpr yexpr cex)
  (gen-and-choice alt (not-expr xexpr) (not-expr yexpr) cex))

(defthm gen-or-options
   (iff (eval-expr (gen-or alt xexpr yexpr cex) env)
        (eval-expr (let ((choice (gen-or-choice alt xexpr yexpr cex)))
                     (let ((xval (eval-expr xexpr cex))
                           (yval (eval-expr yexpr cex)))
                       (cond
                        (alt
                         (if (and (not xval) (not yval))
                             (cond
                              ((equal choice :left)  xexpr)
                              ((equal choice :right) yexpr)
                              (t                     (or-expr xexpr yexpr)))
                           (cond
                              ((equal choice :left)   (or-expr xexpr (not-expr (domain-restriction (not-expr xexpr) (not-expr yexpr) cex))))
                              ((equal choice :right)  (or-expr (not-expr (domain-restriction (not-expr yexpr) (not-expr xexpr) cex)) yexpr))
                              (t                      (or-expr xexpr yexpr)))))
                        (t
                         (if (not xval)
                             (if (not yval) 
                                 (cond
                                  ((equal choice :left)  (or-expr xexpr (not-expr (domain-restriction (not-expr xexpr) (not-expr yexpr) cex))))
                                  ((equal choice :right) (or-expr (not-expr (domain-restriction (not-expr yexpr) (not-expr xexpr) cex)) yexpr))
                                  (t (or-expr xexpr yexpr)))
                               (cond
                                ((equal choice :right) yexpr)
                                (t (or-expr xexpr yexpr))))
                           (if (not yval) 
                               (cond
                                ((equal choice :left) xexpr)
                                (t (or-expr xexpr yexpr)))
                             (cond
                              ((equal choice :left) xexpr)
                              ((equal choice :right) yexpr)
                              (t (or-expr xexpr yexpr))))))))) env)))

(in-theory (disable gen-or))
(in-theory (disable gen-or-choice))

;; -------------------------------------------------------------------
;;
;; The generalization function is defined in terms of gen-and/gen-or
;;
;; -------------------------------------------------------------------

(defun and-alt (alt xexpr yexpr cex)
  (let ((xval (eval-expr xexpr cex))
        (yval (eval-expr yexpr cex)))
    (if xval
        (if yval
            (mv alt alt)
          (mv (not alt) alt))
      (if yval
          (mv alt (not alt))
        (mv alt alt)))))

(defun or-alt (alt xexpr yexpr cex)
  (met ((xalt yalt) (and-alt alt xexpr yexpr cex))
    (mv yalt xalt)))

(defun gen-expr (alt expr cex)
  (case-match expr
    (('and x y)
     (met ((xalt yalt) (and-alt alt x y cex))
       (let ((genx (gen-expr xalt x cex))
             (geny (gen-expr yalt y cex)))
         (gen-and alt genx geny cex))))
    (('or x y)
     (met ((xalt yalt) (or-alt alt x y cex))
       (let ((genx (gen-expr xalt x cex))
             (geny (gen-expr yalt y cex)))
         (gen-or alt genx geny cex))))
    (('not x)
     (let ((genx (gen-expr alt x cex)))
       (not-expr genx)))
    (& expr)))

;; -------------------------------------------------------------------
;; Our top level-proofs
;; -------------------------------------------------------------------

;;
;; Prove that the counterexample is unaffected by the generalization
;;
(defthm eval-expr-gen-expr-idempotent
  (iff (eval-expr (gen-expr alt expr cex) cex)
       (eval-expr expr cex))
  :hints (("Goal" :induct (gen-expr alt expr cex))))

;;
;; Prove that the generalization is conservative
;;
(defthm gen-is-conservative
  (implies
   (iff (eval-expr expr any) (xor alt (not (eval-expr expr cex))))
   (iff (eval-expr (gen-expr alt expr cex) any)
        (eval-expr expr any)))
  :otf-flg t
  :hints (("Goal" :induct (gen-expr alt expr cex)
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t)))

|#
