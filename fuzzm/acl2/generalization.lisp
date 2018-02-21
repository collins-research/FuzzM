;; 
;; Copyright (C) 2017, Rockwell Collins
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;; 
;; 
(in-package "ACL2")
;; -------------------------------------------------------------------
;;
;; A proof of the correctness of a generalization specification.
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

(in-theory (disable not-expr))
(in-theory (disable and-expr))
(in-theory (disable or-expr))

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

;; I introduce the function "bad-spec" to use as a flag indicating
;; where our original spec went wrong.
(defstub bad-spec () nil)

;; We use encapsulation to constrain the possible behaviors of
;; gen-and.  The gen-and-choice function is intended to reflect the
;; freedom we have in choosing behaviors for gen-and.
(encapsulate
 (
  ((gen-and * * *) => *)
  ((gen-and-choice * * *) => *)
  )

 (local 
  (defun gen-and-choice (xexpr yexpr cex) 
    (let ((xval (eval-expr xexpr cex))
          (yval (eval-expr yexpr cex)))
      (cond
       ((and xval yval)
        :both)
       (xval
        :right)
       (t
        :left)))))

 (local 
  (defun gen-and (xexpr yexpr cex) 
    (let ((choice (gen-and-choice xexpr yexpr cex)))
      (cond
       ((equal choice :left)  xexpr)
       ((equal choice :right) yexpr)
       (t (and-expr xexpr yexpr))))))

 ;; It is surprising to me that, if we allow any generalization at
 ;; all, it is not OK for certain default behaviors to be "do nothing"
 ;; (See the "bad-spec" branches below)
 (defthm gen-and-options
   (equal (eval-expr (gen-and xexpr yexpr cex) env)
          (eval-expr (let ((choice (gen-and-choice xexpr yexpr cex)))
                       (let ((xval (eval-expr xexpr cex))
                             (yval (eval-expr yexpr cex)))
                         (if xval
                             (if yval 
                                 (cond
                                  ((equal choice :left)  (and-expr xexpr (domain-restriction xexpr yexpr cex)))
                                  ((equal choice :right) (and-expr (domain-restriction yexpr xexpr cex) yexpr))
                                  (t (and-expr xexpr yexpr)))
                               (if (bad-spec)
                                   (cond
                                    ((equal choice :right) yexpr)
                                    (t (and-expr xexpr yexpr)))
                                 yexpr))
                           (if yval 
                               (if (bad-spec)
                                   (cond
                                    ((equal choice :left) xexpr)
                                    (t (and-expr xexpr yexpr)))
                                 xexpr)
                             (cond
                              ((equal choice :left)  xexpr)
                              ((equal choice :right) yexpr)
                              (t (and-expr xexpr yexpr))))))) env)))

 )

;; -------------------------------------------------------------------
;;
;; The behavior of 'or' is simply the dual of 'and'
;;
;; -------------------------------------------------------------------

(defun gen-or (genx geny cex)
  (not-expr (gen-and (not-expr genx) (not-expr geny) cex)))

(defun gen-or-choice (xexpr yexpr cex)
  (gen-and-choice (not-expr xexpr) (not-expr yexpr) cex))

(defthm gen-or-options
   (iff (eval-expr (gen-or xexpr yexpr cex) env)
        (eval-expr (let ((choice (gen-or-choice xexpr yexpr cex)))
                     (let ((xval (eval-expr xexpr cex))
                           (yval (eval-expr yexpr cex)))
                       (if (not xval)
                           (if (not yval) 
                               (cond
                                ((equal choice :left)  (or-expr xexpr (not-expr (domain-restriction (not-expr xexpr) (not-expr yexpr) cex))))
                                ((equal choice :right) (or-expr (not-expr (domain-restriction (not-expr yexpr) (not-expr xexpr) cex)) yexpr))
                                (t (or-expr xexpr yexpr)))
                             (if (bad-spec)
                                 (cond
                                  ((equal choice :right) yexpr)
                                  (t (or-expr xexpr yexpr)))
                               yexpr))
                         (if (not yval) 
                             (if (bad-spec)
                                 (cond
                                  ((equal choice :left) xexpr)
                                  (t (or-expr xexpr yexpr)))
                               xexpr)
                           (cond
                            ((equal choice :left) xexpr)
                            ((equal choice :right) yexpr)
                            (t (or-expr xexpr yexpr))))))) env)))
   
(in-theory (disable gen-or))
(in-theory (disable gen-or-choice))

;; -------------------------------------------------------------------
;;
;; The generalization function is defined in terms of gen-and/gen-or
;;
;; -------------------------------------------------------------------

(defun gen-expr (expr cex)
  (case-match expr
    (('and x y)
     (let ((genx (gen-expr x cex))
           (geny (gen-expr y cex)))
       (gen-and genx geny cex)))
    (('or x y)
     (let ((genx (gen-expr x cex))
           (geny (gen-expr y cex)))
       (gen-or genx geny cex)))
    (('not x)
     (let ((genx (gen-expr x cex)))
       (not-expr genx)))
    (& expr)))

;; -------------------------------------------------------------------
;; Our top level-proofs
;; -------------------------------------------------------------------

;;
;; Prove that the counterexample is unaffected by the generalization
;;
(defthm eval-expr-gen-expr-idempotent
  (iff (eval-expr (gen-expr expr cex) cex)
       (eval-expr expr cex))
  :hints (("Goal" :induct (gen-expr expr cex))))

;;
;; Prove that the generalization is conservative
;;
(defthm gen-is-conservative
  (implies
   (and
    (not (bad-spec))
    (iff (eval-expr expr any) (not (eval-expr expr cex))))
   (iff (eval-expr (gen-expr expr cex) any)
        (eval-expr expr any)))
  :hints (("Goal" :induct (gen-expr expr cex)
           :do-not-induct t)))
