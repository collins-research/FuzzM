;; 
;; Copyright (C) 2017, Rockwell Collins
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;; 
;; 
(in-package "ACL2")
(include-book "poly")

(defmacro def::signatured (fn &rest args)
  `(encapsulate
       ()
     (def::signature ,fn ,@args)
     (in-theory (disable ,fn))
     ))

(defund lt-op-p (op)
  (declare (type t op))
  (cond
   ((equal op '<)  t)
   ((equal op '<=) t)
   (t nil)))

(defund gt-op-p (op)
  (declare (type t op))
  (cond
   ((equal op '>) t)
   ((equal op '>=) t)
   (t nil)))

(defund ineq-op-p (op)
  (declare (type t op))
  (or (lt-op-p op)
      (gt-op-p op)))

(def::un similarInequalities (op1 op2)
  (declare (xargs :signature ((ineq-op-p ineq-op-p) booleanp)))
  (iff (gt-op-p op1) (gt-op-p op2)))

(defthm lt-op-implies-ineq-op
  (implies
   (lt-op-p op)
   (ineq-op-p op))
  :hints (("Goal" :in-theory (enable ineq-op-p)))
  :rule-classes (:forward-chaining))

(defthm gt-op-implies-ineq-op
  (implies
   (gt-op-p op)
   (ineq-op-p op))
  :hints (("Goal" :in-theory (enable ineq-op-p)))
  :rule-classes (:forward-chaining))

(defund eq-op-p (op)
  (declare (type t op))
  (cond
   ((equal op '=) t)
   ((equal op '!=) t)
   (t nil)))

(defthm eq-op-implies
  (implies
   (eq-op-p op)
   (or (equal op '=)
       (equal op '!=)))
  :rule-classes (:forward-chaining))

(defund op-p (op)
  (declare (type t op))
  (or (  eq-op-p op)
      (ineq-op-p op)))

(defthm eq-op-implies-op
  (implies
   (eq-op-p op)
   (op-p op))
  :hints (("Goal" :in-theory (enable op-p)))
  :rule-classes (:forward-chaining))

(defthm ineq-op-implies-op
  (implies
   (ineq-op-p op)
   (op-p op))
  :hints (("Goal" :in-theory (enable op-p)))
  :rule-classes (:forward-chaining))

(def::und op-fix (op)
  (declare (xargs :signature ((t) op-p)))
  (if (op-p op) op '<))

(defthm op-p-op-fix
  (implies
   (op-p op)
   (equal (op-fix op) op))
  :hints (("Goal" :in-theory (enable op-fix))))

(defund inclusive-op-p (op)
  (declare (type t op))
  (cond
   ((equal op '<=) t)
   ((equal op '>=) t)
   ((equal op '=)  t)
   (t nil)))

(defund exclusive-op-p (op)
  (declare (type t op))
  (cond
   ((equal op '<) t)
   ((equal op '>) t)
   ((equal op '!=) t)
   (t nil)))

(defund optype-p (x)
  (declare (type t x))
  (or (equal x :and)
      (equal x :or)))

(def::und fix-optype (x)
  (declare (xargs :signature ((t) optype-p)))
  (if (optype-p x) x
    :and))

(defthm optype-p-fix-optype
  (implies
   (optype-p x)
   (equal (fix-optype x) x))
  :hints (("Goal" :in-theory (enable fix-optype))))

(defund relation-p (x)
  (declare (type t x))
  (or (equal x :inclusive)
      (equal x :exclusive)))

;; If x is more restrictive than y return -1
(def::un compareWith (x y)
  (declare (xargs :signature ((relation-p relation-p) tri-p)))
  (if (equal x y) 0
    (if (equal x :exclusive) -1
      1)))

(def::und fix-relation (x)
  (declare (xargs :signature ((t) relation-p)))
  (if (relation-p x) x
    :inclusive))

(defthm relation-p-fix-relation
  (implies
   (relation-p x)
   (equal (fix-relation x) x))
  :hints (("Goal" :in-theory (enable fix-relation))))

(def::und gt-relation-p (relation sig)
  (declare (xargs :signature ((relation-p rationalp) booleanp)))
  (let ((relation (fix-relation relation))
        (sig      (rfix sig)))
    (or (< 0 sig) (and (equal relation :inclusive) (= 0 sig)))))

(def::und lt-relation-p (relation sig)
  (declare (xargs :signature ((relation-p rationalp) booleanp)))
  (let ((relation (fix-relation relation))
        (sig      (rfix sig)))
    (or (< sig 0) (and (equal relation :inclusive) (= 0 sig)))))

(defthm gt-relation-p-negate
  (implies
   (rationalp sig)
   (iff (gt-relation-p relation (- sig))
        (lt-relation-p relation sig)))
  :hints (("Goal" :in-theory (enable gt-relation-p lt-relation-p))))

(def::und op-relation (op)
  (declare (xargs :signature ((op-p) relation-p)))
  (cond
   ((equal op '<=) :inclusive)
   ((equal op '>=) :inclusive)
   ((equal op '=)  :inclusive)
   ((equal op '<)  :exclusive)
   ((equal op '>)  :exclusive)
   ((equal op '!=) :exclusive)
   (t              :exclusive)))

(def::un relative-op (relation op)
  (declare (xargs :signature ((relation-p op-p) op-p)))
  (cond
   ((equal op '<=) (if (eql relation :inclusive) '<= '<))
   ((equal op '>=) (if (eql relation :inclusive) '>= '>))
   ((equal op '=)  (if (eql relation :inclusive) '=  '!=))
   ((equal op '<)  (if (eql relation :inclusive) '<= '<))
   ((equal op '>)  (if (eql relation :inclusive) '>= '>))
   ((equal op '!=) (if (eql relation :inclusive) '=  '!=))
   (t              nil)))

;; ==========================================

(defun variableGreater-p (term)
  (declare (type t term))
  (case-match term
    (('>  x y) (and (natp x) (poly-p y)))
    (('>= x y) (and (natp x) (poly-p y)))
    (& nil)))

(def::und fix-variableGreater (x)
  (declare (xargs :signature ((t) variableGreater-p)))
  (if (variableGreater-p x) x
    `(> 0 nil)))

(defthm variableGrater-fix-variableGreater
  (implies
   (variableGreater-p x)
   (equal (fix-variableGreater x) x))
  :hints (("Goal" :in-theory (enable fix-variableGreater))))

(defun variableLess-p (term)
  (declare (type t term))
  (case-match term
    (('<  x y) (and (natp x) (poly-p y)))
    (('<= x y) (and (natp x) (poly-p y)))
    (& nil)))

(def::und fix-variableLess (x)
  (declare (xargs :signature ((t) variableLess-p)))
  (if (variableLess-p x) x
    `(< 0 nil)))

(defthm variableGrater-fix-variableLess
  (implies
   (variableLess-p x)
   (equal (fix-variableLess x) x))
  :hints (("Goal" :in-theory (enable fix-variableLess))))

(defthm less-is-not-greater
  (implies
   (variableLess-p x)
   (not (variableGreater-p x)))
  :rule-classes (:forward-chaining))

(defthm greater-is-not-less
  (implies
   (variableGreater-p x)
   (not (variableLess-p x)))
  :rule-classes (:forward-chaining))

(defun variableInequality-p (term)
  (declare (type t term))
  (or (variableGreater-p term)
      (variableLess-p term)))

(defthm variableLess-implies-variableInequality
  (implies
   (variableLess-p term)
   (variableInequality-p term))
  :rule-classes (:forward-chaining))

(defthm variableGreater-implies-variableInequality
  (implies
   (variableGreater-p term)
   (variableInequality-p term))
  :rule-classes (:forward-chaining))

(defthm variableInequality-implies
  (implies
   (variableInequality-p term)
   (or (variableGreater-p term)
       (variableLess-p term)))
  :rule-classes (:forward-chaining))

(defun variableEquality-p (term)
  (declare (type t term))
  (case-match term
    (('=  x y) (and (natp x) (poly-p y)))
    (('!= x y) (and (natp x) (poly-p y)))
    (& nil)))

(defthm variableEquality-not-variableInequality
  (implies
   (variableEquality-p term)
   (not (variableInequality-p term)))
  :rule-classes (:forward-chaining))

(defthm variableInequality-not-variableEquality
  (implies
   (variableInequality-p term)
   (not (variableEquality-p term)))
  :rule-classes (:forward-chaining))

(defun variableRelation-p (term)
  (declare (type t term))
  (or (variableInequality-p term)
      (variableEquality-p term)))

(defthm variableInequality-implies-variableRelation
  (implies
   (variableInequality-p term)
   (variableRelation-p term))
  :rule-classes (:forward-chaining))

(defthm variableEquality-implies-variableRelation
  (implies
   (variableEquality-p term)
   (variableRelation-p term))
  :rule-classes (:forward-chaining))

(defthm variableRelation-implication
  (implies
   (variableRelation-p term)
   (or (variableInequality-p term)
       (variableEquality-p term)))
  :rule-classes (:forward-chaining))

(def::un relation-varid (term)
  (declare (xargs :signature ((variableRelation-p) natp)))
  (case-match term
    ((& x &) (nfix x))
    (& 0)))

(def::signatured relation-varid (t) natp)

(def::un relation-poly (term)
  (declare (xargs :signature ((variableRelation-p) poly-p)))
  (case-match term
    ((& & y) (poly-fix y))
    (& nil)))

(def::signatured relation-poly (t) poly-p)

(def::un relation-op (term)
  (declare (xargs :signature ((VariableRelation-p) op-p)))
  (case-match term
    ((op & &) (op-fix op))
    (& '<)))

(def::signature relation-op (t) op-p)

(def::un variableRelation (op var poly)
  (declare (xargs :signature ((t t t) variableRelation-p)))
  `(,(op-fix op) ,(nfix var) ,(poly-fix poly)))

(defthm relation-poly-variablerelation
  (equal (relation-poly (variableRelation op var poly))
         (poly-fix poly))
  :hints (("Goal" :in-theory (enable relation-poly))))

(defthm relation-op-variablerelation
  (equal (relation-op (variableRelation op var poly))
         (op-fix op))
  :hints (("Goal" :in-theory (enable relation-op))))

(defthm relation-varid-variablerelation
  (equal (relation-varid (variableRelation op var poly))
         (nfix var))
  :hints (("Goal" :in-theory (enable relation-varid))))

(def::signature variableRelation (lt-op-p t t) variableLess-p)
(def::signature variableRelation (gt-op-p t t) variableGreater-p)
(def::signature variableRelation (eq-op-p t t) variableEquality-p)

(def::signature relation-op (variableGreater-p)    gt-op-p)
(def::signature relation-op (variableLess-p)       lt-op-p)
(def::signature relation-op (variableEquality-p)   eq-op-p)
(def::signature relation-op (variableInequality-p) ineq-op-p)

(def::un variableLess (var relation poly)
  (declare (xargs :signature ((natp relation-p poly-p) variableLess-p)))
  (variableRelation (relative-op (fix-relation relation) '<) var poly))

(def::signature variableLess (t t t) variableLess-p)

(def::un variableGreater (var relation poly)
  (declare (xargs :signature ((natp relation-p poly-p) variableGreater-p)))
  (variableRelation (relative-op (fix-relation relation) '>) var poly))

(def::signature variableGreater (t t t) variableGreater-p)

(def::un variableEquality (var relation poly)
  (declare (xargs :signature ((natp relation-p poly-p) variableEquality-p)))
  (variableRelation (relative-op (fix-relation relation) '=) var poly))

(def::signature variableEquality (t t t) variableEquality-p)

(defthm variableEquality-implies-eq-op
  (implies
   (variableEquality-p term)
   (eq-op-p (relation-op term)))
  :rule-classes (:forward-chaining))

(defun variableInterval-p (term)
  (declare (type t term))
  (case-match term
    (('and gt lt) (and (variableGreater-p gt) (variableLess-p lt)))
    (('or  gt lt) (and (variableGreater-p gt) (variableLess-p lt)))
    (& nil)))

(defthm variableInterval-not-variableRelation
  (implies
   (variableInterval-p term)
   (not (variableRelation-p term)))
  :rule-classes (:forward-chaining))

(defthm variableRelation-not-variableInterval
  (implies
   (variableRelation-p term)
   (not (variableInterval-p term)))
  :rule-classes (:forward-chaining))

(def::und interval-lt (term)
  (declare (xargs :signature ((variableInterval-p) variableLess-p)))
  (case-match term
    (('and & lt) lt)
    (('or  & lt) lt)
    (& nil)))

(def::und interval-gt (term)
  (declare (xargs :signature ((variableInterval-p) variableGreater-p)))
  (case-match term
    (('and gt &) gt)
    (('or  gt &) gt)
    (& nil)))

(def::und interval-optype (term)
  (declare (xargs :signature ((variableInterval-p) optype-p)))
  (case-match term
    (('and & &) :and)
    (('or  & &) :or)
    (& nil)))
  
(def::un variableInterval (gt lt optype)
  (declare (xargs :signature ((t t t) variableInterval-p)))
  (let ((optype (fix-optype optype))
        (gt     (fix-variableGreater gt))
        (lt     (fix-variableLess lt)))
    (if (equal optype :and)
        `(and ,gt ,lt)
      `(or ,gt ,lt))))

(defthm interval-optype-variableInterval
  (equal (interval-optype (variableInterval gt lt optype))
         (fix-optype optype))
  :hints (("Goal" :in-theory (enable interval-optype variableInterval))))

(defthm interval-gt-variableInterval
  (equal (interval-gt (variableInterval gt lt optype))
         (fix-variableGreater gt))
  :hints (("Goal" :in-theory (enable interval-gt variableInterval))))

(defthm interval-lt-variableInterval
  (equal (interval-lt (variableInterval gt lt optype))
         (fix-variableLess lt))
  :hints (("Goal" :in-theory (enable interval-lt variableInterval))))

;; ============================

(defun variablebound-p (term)
  (declare (type t term))
  (or (variableInterval-p term)
      (variableRelation-p term)))

(defthm variableInterval-implies-variableBound
  (implies
   (variableInterval-p term)
   (variableBound-p term))
  :rule-classes (:forward-chaining))

(defthm variableRelation-implies-variableBound
  (implies
   (variableRelation-p term)
   (variableBound-p term))
  :rule-classes (:forward-chaining))

(defthm variableBound-implication
  (implies
   (variableBound-p term)
   (or (variableInterval-p term)
       (variableRelation-p term)))
  :rule-classes (:forward-chaining))

(def::un bound-varid (term)
  (declare (xargs :signature ((variableBound-p) natp)))
  (if (variableInterval-p term)
      (relation-varid (interval-gt term))
    (relation-varid term)))

(def::signature bound-varid (t) natp)

(defun wf-variableBound (term)
  (declare (type t term))
  (and (variableBound-p term)
       (if (variableInterval-p term)
           (equal (relation-varid (interval-gt term))
                  (relation-varid (interval-lt term)))
         t)))

(in-theory (disable variableRelation relation-op))
(in-theory (disable variableRelation-p variableEquality-p variableInequality-p variableGreater-p variableLess-p))
(in-theory (disable variableInterval interval-lt interval-gt interval-optype))
(in-theory (disable variableInterval-p))
(in-theory (disable variableBound-p))

(defthm eval-ineq-variableRelationp
  (implies
   (variableRelation-p term)
   (equal (eval-ineq term env)
          (let ((op (relation-op term)))
            (if (equal (op-relation op) :inclusive)
                (cond
                 ((lt-op-p op)
                  (<= (get-binding (relation-varid term) env)
                      (poly-eval (relation-poly term) env)))
                 ((gt-op-p op)
                  (>= (get-binding (relation-varid term) env)
                      (poly-eval (relation-poly term) env)))
                 (t
                  (equal (get-binding (relation-varid term) env)
                         (poly-eval (relation-poly term) env))))
              (cond
               ((lt-op-p op)
                (<  (get-binding (relation-varid term) env)
                    (poly-eval (relation-poly term) env)))
               ((gt-op-p op)
                (> (get-binding (relation-varid term) env)
                   (poly-eval (relation-poly term) env)))
               (t
                (not (equal (get-binding (relation-varid term) env)
                            (poly-eval (relation-poly term) env)))))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable eval-ineq relation-op relation-varid relation-poly variableRelation-p 
                              variableEquality-p variableInequality-p variableLess-p variableGreater-p))))

(defthm eval-ineq-variableIntervalp
  (implies
   (variableInterval-p term)
   (equal (eval-ineq term env)
          (if (equal (interval-optype term) :and)
              (and (eval-ineq (interval-gt term) env)
                 (eval-ineq (interval-lt term) env))
            (or (eval-ineq (interval-gt term) env)
                (eval-ineq (interval-lt term) env)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable eval-ineq interval-optype interval-gt interval-lt variableInterval-p))))

(in-theory (disable relation-p signum))

(defthm similarinequalities-variableless
  (implies
   (and
    (variableless-p x)
    (variableless-p y))
   (similarinequalities (relation-op x)
                        (relation-op y)))
  :hints (("goal" :in-theory (enable similarinequalities)))
  :rule-classes (:type-prescription))

(defthm similarinequalities-variablegreater
  (implies
   (and
    (variablegreater-p x)
    (variablegreater-p y))
   (similarinequalities (relation-op x)
                        (relation-op y)))
  :hints (("goal" :in-theory (enable similarinequalities)))
  :rule-classes (:type-prescription))

(defun variableBound-listp (list)
  (declare (type t list))
  (if (not (consp list)) (null list)
    (and (variableBound-p (car list))
         (variableBound-listp (cdr list)))))

(defthm true-listp-variableBound-listp
  (implies
   (variableBound-listp list)
   (true-listp list))
  :rule-classes (:forward-chaining))

(defthm variableBound-listp-append
  (implies
   (and
    (variableBound-listp x)
    (variableBound-listp y))
   (variableBound-listp (append x y))))

(defun conjoinResults (x list)
  (declare (type t x list))
  (if (not (consp list)) x
    `(and ,x ,(conjoinResults (car list) (cdr list)))))

(defthm eval-ineq-and
  (equal (eval-ineq (cons 'and (cons x (cons y nil))) env)
         (and (eval-ineq x env)
              (eval-ineq y env)))
  :hints (("Goal" :in-theory (enable eval-ineq))))


(in-theory (enable signum))

(def::un compareTo (x y)
  (declare (xargs :signature ((rationalp rationalp) tri-p)))
  (signum (- x y)))

(in-theory (enable gt-op-p lt-op-p))

(defthm variablegreater-from-variableinequality
  (implies
   (and
    (variableinequality-p x)
    (gt-op-p (relation-op x)))
   (variablegreater-p x)))

(defthm variableless-from-variableinequality
  (implies
   (and
    (variableinequality-p x)
    (lt-op-p (relation-op x)))
   (variableless-p x)))

(defthmd destructure-conjoinresults-helper-1
  (equal (eval-ineq (conjoinresults z (append x y)) cex)
         (and (eval-ineq (conjoinresults z x) cex)
              (eval-ineq (conjoinresults z y) cex))))

(def::un bound-append (x y)
  (declare (xargs :signature ((variableBound-listp variableBound-listp) variableBound-listp)))
  (append x y))

(defthm destructure-conjoinresults
  (implies
   (and
    (force (variableGreater-p gt))
    (force (variableLess-p lt)))
   (equal (eval-ineq (conjoinresults (variableinterval gt lt :and)
                                     (bound-append gtres ltres)) cex)
          (and (eval-ineq (conjoinresults gt gtres) cex)
               (eval-ineq (conjoinresults lt ltres) cex))))
  :hints (("Goal" :in-theory (e/d (variableinterval destructure-conjoinresults-helper-1)
                                  (EVAL-INEQ-VARIABLERELATIONP))
           :expand ((:free (lt) (conjoinresults lt ltres))
                    (:free (gt) (conjoinresults gt gtres)))
           :do-not-induct t)))

(in-theory (disable bound-append))

