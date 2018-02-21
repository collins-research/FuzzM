;; 
;; Copyright (C) 2017, Rockwell Collins
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;; 
;; 
(in-package "ACL2")
(include-book "gen3")

;;
;; We should consider supporting cnf of all false.
;; This would be nice because it has a nice restricted form.
;; (~ (and (or x a) (or x b)) (or x a b))
;;
;; (and (or x a b) (or x c d))
;; (iff (or (and (not a) (not b)) c d)
;;      (and (or (not a) c d) (or (not b) c d)))
;;
;; We need to ensure that all of the constraints are true (cex) ..
;; (or t t t) (or t nil nil)
;; 
;; (or t nil nil) (or t nil nil)
;;
;; If the (a b) are both true and (or c d) is true, 

;;
;; Assuming all clauses are true ..
;;
;; - if x is false, we can drop x from either <and avoid any conflict>
;; - we can always drop any false (a b)
;; - if (a b) are true, we can drop x from (or x c d)
;; - 

;; You can always just drop false clauses ..

(def::un all-false-term-listp (x)
  (declare (xargs :signature ((boolean-term-listp) booleanp)))
  (not (or-list (evcex-list x))))

(def::un all-true-term-listp (x)
  (declare (xargs :signature ((boolean-term-listp) booleanp)))
  (and-list (evcex-list x)))

(def::un negate-and-or (x y)
  (declare (xargs :signature ((boolean-term-listp boolean-term-listp) clause-listp)))
  (if (endp x) nil
    (cons (clause (tag nil) (cons (not-expr (car x)) y))
          (negate-and-or (cdr x) y))))

;; From 'and' you can drop false (unless mixed .. you must drop  true)
;; From 'or'  you can drop true  (unless mixed .. you must drop false)

;; Assuming both evaluate to true ..

(defthm evcex-negate-and-or
  (implies
   (and
    (boolean-term-listp x)
    (boolean-term-listp y))
   (iff (and-list (evcex-list (negate-and-or x y)))
        (or (not (or-list (evcex-list x)))
            (or-list (evcex-list y))))))

(defthm evalt-negate-and-or
  (implies
   (and
    (boolean-term-listp x)
    (boolean-term-listp y))
   (iff (and-list (evalt-list (negate-and-or x y) env))
        (or (not (or-list (evalt-list x env)))
            (or-list (evalt-list y env)))))) 

;; what happens when:
;; (not (all-false-term-listp x))
;; (all-false-term-listp y)
;; .. well, we can swap the two terms.

(def::und and-x-y-z-1 (x y z)
  (declare (xargs :signature ((boolean-term-p boolean-term-listp boolean-term-listp) clause-p clause-listp)))
  (if (or (all-false-term-listp y) (not (all-false-term-listp z)))
      (mv (clause (tag nil) (cons x y)) (negate-and-or y z))
    (mv (clause (tag nil) (cons x z)) (negate-and-or z y))))

(defthm evcex-and-x-y-z-1
  (implies
   (and
    (boolean-term-p x)
    (boolean-term-listp y)
    (boolean-term-listp z)
    (or (evcex x) (or-list (evcex-list y)))
    (or (evcex x) (or-list (evcex-list z))))
   (and (evcex (val 0 (and-x-y-z-1 x y z)))
        (and-list (evcex-list (val 1 (and-x-y-z-1 x y z))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable and-x-y-z-1))))

(defthm evalt-and-x-y-z-1
  (implies
   (and
    (boolean-term-p x)
    (boolean-term-listp y)
    (boolean-term-listp z)
    (or (evcex x) (or-list (evcex-list y)))
    (or (evcex x) (or-list (evcex-list z)))
    (not (and (or (evalt x env) (or-list (evalt-list y env)))
              (or (evalt x env) (or-list (evalt-list z env))))))
   (not (and (evalt (val 0 (and-x-y-z-1 x y z)) env)
             (and-list (evalt-list (val 1 (and-x-y-z-1 x y z)) env)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable and-x-y-z-1))))

(def::un c (z)
  (declare (xargs :signature ((boolean-term-listp) clause-listp)))
  (list (clause (tag nil) z)))

(def::un choose-a-true-term (list)
  (declare (xargs :signature ((boolean-term-listp) boolean-term-p)))
  (if (not (consp list)) `(id :x t)
    (if (evcex (car list)) (car list)
      (choose-a-true-term (cdr list)))))

(defthm evcex-choose-a-true-term
  (implies
   (boolean-term-listp list)
   (evcex (choose-a-true-term list))))

(defthm evalt-choose-a-true-term
  (implies
   (and
    (and-list (not-list (evalt-list z env)))
    (not (all-false-term-listp z)))
   (not (evalt (choose-a-true-term z) env))))

(encapsulate
    (
     (arbitrary-choice (x y z) t :guard t)
     )
  (local
   (defun arbitrary-choice (x y z)
     (declare (type t x y z))
     (list x y z)))
  )

(def::un and-x-y-z-2 (x y z)
  (declare (xargs :signature ((boolean-term-p boolean-term-listp boolean-term-listp) clause-p clause-listp)))
  (let ((choice (arbitrary-choice x y z)))
    (cond
     ((and (equal choice 1)
           (not (evcex x)))
      (if (lexorder x y)
          (mv (clause (tag nil) (cons x y)) (c z))
        (mv (clause (tag nil) (cons x z)) (c y))))
     ((and (equal choice 2)
           (all-false-term-listp y))
      (mv (clause (tag nil) (list x)) nil))
     ((and (equal choice 3)
           (all-false-term-listp z))
      (mv (clause (tag nil) (list x)) nil))
     ((and (equal choice 4)
           (not (all-false-term-listp y))
           (not (all-false-term-listp z))
           (evcex x))
      (if (lexorder x y)
          (mv (clause (tag nil) (cons x y)) (c z))
        (mv (clause (tag nil) (cons x z)) (c y))))
     (t
      (and-x-y-z-1 x y z)))))

;; (and tx ty) = (and tx ty)
;; (and fx ty) = fx
;; (and fx fy) = fx | fy | (and fx fy)

(defthm evcex-and-x-y-z-2
  (implies
   (and
    (boolean-term-p x)
    (boolean-term-listp y)
    (boolean-term-listp z)
    (or (evcex x) (or-list (evcex-list y)))
    (or (evcex x) (or-list (evcex-list z))))
   (and (evcex (val 0 (and-x-y-z-2 x y z)))
        (and-list (evcex-list (val 1 (and-x-y-z-2 x y z))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable and-x-y-z-2))))

(defthm evalt-and-x-y-z-2
  (implies
   (and
    (boolean-term-p x)
    (boolean-term-listp y)
    (boolean-term-listp z)
    (or (evcex x) (or-list (evcex-list y)))
    (or (evcex x) (or-list (evcex-list z)))
    (not (and (or (evalt x env) (or-list (evalt-list y env)))
              (or (evalt x env) (or-list (evalt-list z env))))))
   (not (and (evalt (val 0 (and-x-y-z-2 x y z)) env)
             (and-list (evalt-list (val 1 (and-x-y-z-2 x y z)) env)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable and-x-y-z-2 and-x-y-z-1))))


;; (iff (evcex-list (extract-features x))
;;      (evcex-list (identify-features x)))

;; ((features ) (non-features ))

;; (defun and-clist (x y)
;;   (let ((x (keep-false-and-features x))
;;         (y (keep-false-and-features y)))
;;     (append x y)))

;; (:features :non-features)

      
;; (and (+ (or a b c d)) (- (and y z)))

;; ;; If you ever see a (+) you can always just replace the term with its
;; ;; cex .. expand it completely.

;; (defun and+ (x y)
;;   ((or (and (ev x) (ev y))
;;        (not (and (ev x) (ev y))))
;;    (and+ x y))
;;   (..)

;; (defun and- (x y)
;;   )

;; (defun not (x)
;;   )

;; (a+ x)
;; (a- x)

;; (a+ (and x y))
;; (and (a- x) (a+ x))

;; (defun size (x)
;;   (if (abstraction-p x)
;;       (acl2-count (abstraction-expr x))
;;     (acl2-count x)))

;; (def::un and (dir x dir y)
;;   )

;; ;; It is not clear that an efficient algorithm exists to do this.
;; ;; The issue is that, just because,

;; (and x (and y (and p q)))

;; (and .. (a+ x) .. (a- y))

;; (defun and-expr (x y)
;;   (if (always-true x) y
;;     (if (always-true y) x
;;       (if (always-false x) x
;;         (if (always-false y) y
;;           (and a b) (and c d)
;;           (and a (and c (and-rec b d)))

;; (defun not-expr (x)
;;   ..)


;; (a+ (and x y))

;; (defun and-and-and (x y)
;;   (pattern::let (((and a b) x)
;;                  ((and c d) y))
;;     (and-expr (and a c) (and b d))))

;; (defun and (x y)
;;   (cond
;;    ((and (and-op x)
;;          (and-op y))
;;     (and-and-and x y))
;;    ((and (and-op x)
;;          (not (and-op y)))
;;     (and-and-or x y))
;;    ((and (not (and-op x))
;;          (and-op y))
;;     (and-and-or y x))
;;    (t
;;     (and-or-or x y))))

;; (defun and-gen (x+ x- y+ y-)
;;   (cond
;;    ((iff (ev x) (ev y))
;;     (mv (and (a- x-) (a- y-)) 
;;         (and (a+ x+) (a+ y+))))
;;    ((not (ev x)) ;; (ev y)
;;     (mv (and (a- x-) (a+ y+)) 
;;         (and (a+ x+) (a- y-))))
;;    (t ;; (not (ev y)) (ev x)
;;     (mv (and (a+ x+) (a- y-)) 
;;         (and (a- x-) (a+ y+))))))

;; (defun gen (f)
;;   (case-match f
;;     `((and x y)
;;       (met ((x- x+) (gen x))
;;         (met ((y- y+) (gen y))
;;           (and-gen x+ x- y+ y-))))
;;     `((not x)
;;       (met ((z- z+) (gen x))
;;         (mv (not-expr z-) (not-expr z+))))
;;     (& 
;;      (mv f f))))

;; (val 0 (gen f))

;; (val 1 (gen f))

;; (and+ arg)
;; (and- arg)



