;; 
;; Copyright (C) 2017, Rockwell Collins
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;; 
;; 
(in-package "ACL2")
(include-book "generalization")

(defun eval-trap (trap env)
  (if (not (consp trap)) t
    (let ((entry (car trap)))
      (and (eval-expr entry env)
           (eval-trap (cdr trap) env)))))

(encapsulate
    (
     ((choose-a-false-expr * *) => *)
     )
  
  (local (defun choose-a-false-expr (trap cex)
           (if (eval-trap trap cex) (if (consp trap) (car trap) t)
             (if (endp trap) nil
               (let ((entry (car trap)))
                 (if (not (eval-expr entry cex)) entry
                   (choose-a-false-expr (cdr trap) cex)))))))
  
  (defthm choose-a-false-expr-property
    (iff (eval-expr (choose-a-false-expr trap cex) cex)
         (eval-trap trap cex)))
  
  (defthm any-true-is-still-true
    (implies
     (eval-trap trap any)
     (eval-expr (choose-a-false-expr trap cex) any)))
  
  )

(encapsulate
    (
     ((choose-a-true-expr * *) => *)
     )
  
  (local (defun choose-a-true-expr (trap cex)
           (if (endp trap) t
             (let ((entry (car trap)))
               (if (eval-expr entry cex) entry
                 (choose-a-true-expr (cdr trap) cex))))))
  
  (defthm choose-a-true-expr-property
    (implies
     (eval-trap trap cex)
     (eval-expr (choose-a-true-expr trap cex) cex)))
  
  #+joe
  (defthm any-true-is-still-true
    (implies
     (eval-trap trap any)
     (eval-expr (choose-a-true-expr trap cex) any)))
  
  )

(defun not-trap (trap)
  (if (not (consp trap)) nil
    (let ((entry (car trap)))
      (cons (not-expr entry)
            (not-trap (cdr trap))))))

(defun single-trap-p (trap)
  (and (consp trap)
       (not (consp (cdr trap)))))

(defthm single-not
  (implies
   (single-trap-p trap)
   (iff (eval-trap (not-trap trap) env)
        (not (eval-trap trap env)))))

(in-theory (disable single-trap-p))

;; ---------------------------------------------------------------
;; top-level operations
;; ---------------------------------------------------------------

(defun eval-top (top env)
  (case-match top
    ((':negated trap)
     (not (eval-trap trap env)))
    (&
     (eval-trap (cadr top) env))))

(defun top-body (top)
  (case-match top
    ((':negated trap) trap)
    (& (cadr top))))

(defun negatedp (top)
  (case-match top
    ((':negated &)
     t)
    (& nil)))

(defthm eval-top-negated
  (implies
   (negatedp top)
   (iff (eval-top top env)
        (not (eval-trap (top-body top) env)))))

(defthm eval-top-body
  (implies
   (not (negatedp top))
   (iff (eval-top top env)
        (eval-trap (top-body top) env))))

(defun entrap (trap)
  `(:true ,trap))

(defthm eval-top-entrap
  (iff (eval-top (entrap trap) env)
       (eval-trap trap env)))

(defun nottrap (trap)
  `(:negated ,trap))

(defun singlep (top)
  (single-trap-p (top-body top)))

(defun not-top (top)
  (if (negatedp top) (entrap (top-body top))
    (if (singlep top)
        (entrap (not-trap (top-body top)))
      (nottrap (top-body top)))))

(defthm eval-trap-not-top
  (iff (eval-top (not-top top) env)
       (not (eval-top top env)))
  :hints (("Goal" :do-not-induct t)))

(in-theory (disable not-top))
(in-theory (disable entrap nottrap))
(in-theory (disable top-body))
(in-theory (disable singlep))
(in-theory (disable negatedp))
(in-theory (disable eval-top))

;; ---------------------------------------------------------------

(defun single-trap (expr)
  (cons expr nil))

(defthm trap-eval-single-trap
  (iff (eval-trap (single-trap expr) cex)
       (eval-expr expr cex))
  :hints (("Goal" :do-not-induct t)))

(in-theory (disable single-trap))

;; ---------------------------------------------------------------

(defthm mv-nth-to-nth
  (equal (mv-nth x y) (nth x y)))

(encapsulate
    (
     ((gen-expr-and * * *) => (mv * * *))
     )

  (local (defun gen-expr-and (x y env)
           (let ((choice (gen-and-choice x y env)))
             (let ((xval (eval-expr x env))
                   (yval (eval-expr y env)))
               (if xval
                   (if yval 
                       (cond
                        ((equal choice :left)  (mv t (domain-restriction x y env) x))
                        ((equal choice :right) (mv t (domain-restriction y x env) y))
                        (t                     (mv nil t (and-expr x y))))
                     (mv nil nil y))
                 (if yval
                     (mv nil nil x)
                   (cond
                    ((equal choice :left)  (mv nil nil x))
                    ((equal choice :right) (mv nil nil y))
                    (t (mv nil nil (and-expr x y))))))))))

  (defthm gen-expr-and-choice-1
    (implies
     (and
      (eval-expr t1 cex)
      (not (eval-expr t2 cex)))
     (iff (eval-expr (nth 2 (gen-expr-and t1 t2 cex)) any)
          (eval-expr t2 any))))

  (defthm gen-expr-and-choice-2
    (implies
     (and
      (eval-expr t2 cex)
      (not (eval-expr t1 cex)))
     (iff (eval-expr (nth 2 (gen-expr-and t1 t2 cex)) any)
          (eval-expr t1 any))))

  (defthm gen-expr-and-cex-nth-1
    (iff (eval-expr (nth 1 (gen-expr-and t1 t2 cex)) cex)
         (and (eval-expr t1 cex) 
              (eval-expr t2 cex))))
  
  (defthm gen-expr-and-cex-nth-2
    (iff (eval-expr (nth 2 (gen-expr-and t1 t2 cex)) cex)
         (and (eval-expr t1 cex)
              (eval-expr t2 cex))))
  
  (defthm gen-expr-and-0-implies
    (implies
     (nth 0 (gen-expr-and t1 t2 cex))
     (and (eval-expr t1 cex) (eval-expr t2 cex)))
    :rule-classes (:forward-chaining))

  (defthm gen-expr-and-conservative
    (implies
     (and
      (not (nth 0 (gen-expr-and x y cex)))
      (iff (and (eval-expr x any) (eval-expr y any))
           (not (and (eval-expr x cex) (eval-expr y cex)))))
     (iff (eval-expr (nth 2 (gen-expr-and x y cex)) any)
          (and (eval-expr x any) (eval-expr y any)))))

  (defthm gen-expr-and-conservative-1
    (implies
     (and
      (not (eval-expr x any))
      (nth 0 (gen-expr-and t1 t2 cex)))
     (or (not (eval-expr (nth 2 (gen-expr-and x y cex)) any))
         (not (eval-expr (nth 1 (gen-expr-and x y cex)) any))))
    :rule-classes ((:forward-chaining :trigger-terms ((gen-expr-and x y cex)))))

  (defthm gen-expr-and-conservative-2
    (implies
     (and
      (not (eval-expr y any))
      (nth 0 (gen-expr-and t1 t2 cex)))
     (or (not (eval-expr (nth 2 (gen-expr-and x y cex)) any))
         (not (eval-expr (nth 1 (gen-expr-and x y cex)) any))))
    :rule-classes ((:forward-chaining :trigger-terms ((gen-expr-and x y cex)))))

  )

(in-theory (disable nth))

;; ---------------------------------------------------------------

(defstub <-compare (left right) nil)

(defmacro met (bind &rest args)
  `(mv-let ,(car bind) ,(cadr bind)
           ,@args))

(defun gen-trap-and-1 (expr t2 cex)
  (if (endp t2) (single-trap expr)
    (let ((entry (car t2)))
      (if (<-compare expr entry) (cons expr t2)
        (if (<-compare entry expr) (cons entry (gen-trap-and-1 expr (cdr t2) cex))
          (met ((restrict expr entry) (gen-expr-and expr entry cex))
            (if (not restrict) (cons entry (cdr t2))
              (cons entry (gen-trap-and-1 expr (cdr t2) cex)))))))))

(defthm gen-trap-and-1-cex
  (iff (eval-trap (gen-trap-and-1 expr t2 cex) cex)
       (and (eval-expr expr cex)
            (eval-trap t2 cex))))

(defun all-false (trap cex)
  (if (endp trap) t
    (let ((entry (car trap)))
      (and (not (eval-expr entry cex))
           (all-false (cdr trap) cex)))))

(defthm all-false-single-trap
  (iff (all-false (single-trap expr) cex)
       (not (eval-expr expr cex)))
  :hints (("Goal" :in-theory (enable single-trap))))

(defthm all-false-invariant
  (implies
   (and
    (all-false t2 cex)
    (not (eval-expr expr cex)))
   (all-false (gen-trap-and-1 expr t2 cex) cex))
  :hints (("Goal" :induct (gen-trap-and-1 expr t2 cex)))
  :rule-classes ((:forward-chaining :trigger-terms ((gen-trap-and-1 expr t2 cex)))))

(defthm all-false-implication
  (implies
   (all-false t2 cex)
   (or (not (consp t2))
       (not (eval-trap t2 cex))))
  :rule-classes (:forward-chaining))

(defthm gen-trap-and-1-conservative-false
  (implies
   (and 
    (eval-expr expr cex)
    (eval-trap t2 cex)
    (not (and (eval-expr expr any) (eval-trap t2 any))))
   (not (eval-trap (gen-trap-and-1 expr t2 cex) any)))
  :hints (("Goal" :induct (gen-trap-and-1 expr t2 cex))))

(defthm gen-trap-and-1-conservative-true
  (implies
   (and 
    (not (eval-expr expr cex))
    (all-false t2 cex)
    (eval-trap t2 any)
    (eval-expr expr any))
   (eval-trap (gen-trap-and-1 expr t2 cex) any))
  :hints (("Goal" :induct (gen-trap-and-1 expr t2 cex))))

(in-theory (disable gen-trap-and-1))

;; ---------------------------------------------------------------

(defun gen-trap-and (t1 t2 cex)
  (if (endp t1) t2
    (let ((t2 (gen-trap-and (cdr t1) t2 cex)))
      (gen-trap-and-1 (car t1) t2 cex))))

(defthm gen-trap-and-cex
  (iff (eval-trap (gen-trap-and t1 t2 cex) cex)
       (and (eval-trap t1 cex)
            (eval-trap t2 cex))))

(defthm all-false-gen-trap-and
  (implies
   (and
    (all-false t1 cex)
    (all-false t2 cex))
   (all-false (gen-trap-and t1 t2 cex) cex)))

(defthm gen-trap-and-conservative-false
  (implies
   (and
    (eval-trap t1 cex)
    (eval-trap t2 cex)
    (or (not (eval-trap t1 any)) 
        (not (eval-trap t2 any))))
   (not (eval-trap (gen-trap-and t1 t2 cex) any))))

(defthm gen-trap-and-conservative-true
  (implies
   (and
    (all-false t1 cex)
    (all-false t2 cex)
    (eval-trap t1 any)
    (eval-trap t2 any))
   (eval-trap (gen-trap-and t1 t2 cex) any)))

(in-theory (disable gen-trap-and))

;; ---------------------------------------------------------------

(defun gen-top-and-not2 (t1 t2 cex)
  (let ((fexpr1 (choose-a-false-expr (top-body t1) cex))
        (fexpr2 (choose-a-false-expr (top-body t2) cex)))
    (entrap (gen-trap-and (single-trap (not-expr fexpr1)) (single-trap (not-expr fexpr2)) cex))))

(defthm gen-top-and-not2-cex
  (implies
   (and
    (negatedp t1)
    (negatedp t2))
   (iff (eval-top (gen-top-and-not2 t1 t2 cex) cex)
        (and (eval-top t1 cex)
             (eval-top t2 cex))))
  :hints (("Goal" :do-not-induct t)))

(defthm gen-top-and-not2-conservative-false
  (implies
   (and
    (negatedp t1)
    (negatedp t2)
    (or (not (eval-top t1 any)) (not (eval-top t2 any)))
    (eval-top t1 cex)
    (eval-top t2 cex))
   (not (eval-top (gen-top-and-not2 t1 t2 cex) any)))
  :hints (("Goal" :do-not-induct t)))

(in-theory (disable gen-top-and-not2))

;; ---------------------------------------------------------------

(defun gen-top-and-not1 (t1 t2 cex)
  (let ((fexpr (choose-a-false-expr (top-body t1) cex)))
    (entrap (gen-trap-and (single-trap (not-expr fexpr)) (top-body t2) cex))))

(defthm gen-top-and-not1-cex
  (implies
   (and
    (negatedp t1)
    (not (negatedp t2)))
   (iff (eval-top (gen-top-and-not1 t1 t2 cex) cex)
        (and (eval-top t1 cex)
             (eval-top t2 cex))))
  :hints (("Goal" :do-not-induct t)))

(defthm gen-top-and-not1-conservative
  (implies
   (and
    (or (not (eval-top t1 any)) (not (eval-top t2 any)))
    (eval-top t1 cex)
    (eval-top t2 cex)
    (negatedp t1)
    (not (negatedp t2)))
   (not (eval-top (gen-top-and-not1 t1 t2 cex) any)))
  :hints (("Goal" :do-not-induct t)))

(in-theory (disable gen-top-and-not1))

;; ---------------------------------------------------------------

(defun gen-top-and-true (t1 t2 cex)
  (if (not (negatedp t1))
      (if (not (negatedp t2))
          (entrap (gen-trap-and (top-body t1) (top-body t2) cex))
        (gen-top-and-not1 t2 t1 cex))
    (if (not (negatedp t2))
        (gen-top-and-not1 t1 t2 cex)
      (gen-top-and-not2 t1 t2 cex))))

(defthm gen-top-and-true-cex
  (iff (eval-top (gen-top-and-true t1 t2 cex) cex)
       (and (eval-top t1 cex)
            (eval-top t2 cex)))
  :hints (("Goal" :do-not-induct t)))

(defthm gen-top-and-true-conservative
  (implies
   (and
    (or (not (eval-top t1 any)) (not (eval-top t2 any)))
    (eval-top t1 cex)
    (eval-top t2 cex))
   (not (eval-top (gen-top-and-true t1 t2 cex) any)))
  :hints (("Goal" :do-not-induct t)))

(in-theory (disable gen-top-and-true))

;; ---------------------------------------------------------------

(encapsulate
    (
     ((and-choice * * *) => *)
     )

  (local (defun and-choice (t1 t2 cex)
           (declare (ignore t2 cex))
           t1))

  (defthm and-choice-property
    (implies
     (iff (eval-top t1 any) (eval-top t2 any))
     (iff (eval-top (and-choice t1 t2 cex) any)
          (eval-top t1 any))))

  )

(defun gen-top-and-false (t1 t2 cex)
  (if (and (not (negatedp t1))
           (not (negatedp t2))
           (all-false (top-body t1) cex)
           (all-false (top-body t2) cex))
      (entrap (gen-trap-and (top-body t1) (top-body t2) cex))
    (and-choice t1 t2 cex)))

(defthm gen-top-and-false-cex
  (implies
   (and 
    (not (eval-top t1 cex))
    (not (eval-top t2 cex)))
   (not (eval-top (gen-top-and-false t1 t2 cex) cex)))
  :hints (("Goal" :do-not-induct t)))

(defthm gen-top-and-false-conservative
  (implies
   (and
    (eval-top t1 any)
    (eval-top t2 any)
    (not (eval-top t1 cex))
    (not (eval-top t2 cex)))
   (eval-top (gen-top-and-false t1 t2 cex) any))
  :hints (("Goal" :do-not-induct t)))

(in-theory (disable gen-top-and-false))

;; ---------------------------------------------------------------

(defun gen-top-and (t1 t2 cex)
  (if (eval-top t1 cex)
      (if (not (eval-top t2 cex)) t2
        (gen-top-and-true t1 t2 cex))
    (if (eval-top t2 cex) t1
      (gen-top-and-false t1 t2 cex))))

(defthm gen-top-and-cex
  (iff (eval-top (gen-top-and t1 t2 cex) cex)
       (and (eval-top t1 cex)
            (eval-top t2 cex)))
  :hints (("Goal" :do-not-induct t)))

(defthm gen-top-and-conservative
  (implies
   (iff (and (eval-top t1 cex) (eval-top t2 cex))
        (not (and (eval-top t1 any) (eval-top t2 any))))
   (iff (eval-top (gen-top-and t1 t2 cex) any)
        (and (eval-top t1 any)
             (eval-top t2 any)))))

(defthm gen-top-and-choice-1
  (implies
   (and
    (eval-top t1 cex)
    (not (eval-top t2 cex)))
   (iff (eval-top (gen-top-and t1 t2 cex) any)
        (eval-top t2 any))))

(defthm gen-top-and-choice-2
  (implies
   (and
    (eval-top t2 cex)
    (not (eval-top t1 cex)))
   (iff (eval-top (gen-top-and t1 t2 cex) any)
        (eval-top t1 any))))

(in-theory (disable gen-top-and))

;; ---------------------------------------------------------------

(defun gen-top-or (t1 t2 cex)
  (not-top (gen-top-and (not-top t1) (not-top t2) cex)))

(defthm gen-top-or-cex
  (iff (eval-top (gen-top-or t1 t2 cex) cex)
       (or (eval-top t1 cex)
           (eval-top t2 cex)))
  :hints (("Goal" :do-not-induct t)))

(defthm gen-top-or-conservative
  (implies
   (iff (or (eval-top t1 cex) (eval-top t2 cex))
        (not (or (eval-top t1 any) (eval-top t2 any))))
   (iff (eval-top (gen-top-or t1 t2 cex) any)
        (or (eval-top t1 any)
            (eval-top t2 any)))))

(defthm gen-top-or-choice-1
  (implies
   (and
    (eval-top t1 cex)
    (not (eval-top t2 cex)))
   (iff (eval-top (gen-top-or t1 t2 cex) any)
        (eval-top t1 any))))

(defthm gen-top-or-choice-2
  (implies
   (and
    (eval-top t2 cex)
    (not (eval-top t1 cex)))
   (iff (eval-top (gen-top-or t1 t2 cex) any)
        (eval-top t2 any))))

(in-theory (disable gen-top-or))

;; ---------------------------------------------------------------
;; Top-level trapezoidal generalization
;; ---------------------------------------------------------------

(defun trap-gen (expr cex)
  (case-match expr
    (('and x y)
     (let ((genx (trap-gen x cex))
           (geny (trap-gen y cex)))
       (gen-top-and genx geny cex)))
    (('or x y)
     (let ((genx (trap-gen x cex))
           (geny (trap-gen y cex)))
       (gen-top-or genx geny cex)))
    (('not x)
     (let ((genx (trap-gen x cex)))
       (not-top genx)))
    (& (entrap (single-trap expr)))))

(defthm trap-gen-cex
  (iff (eval-top (trap-gen expr cex) cex)
       (eval-expr expr cex)))

(defthm trap-gen-is-conservative
  (implies
   (iff (eval-expr expr any) (not (eval-expr expr cex)))
   (iff (eval-top (trap-gen expr cex) any)
        (eval-expr expr any))))

