;; 
;; Copyright (C) 2017, Rockwell Collins
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;; 
;; 
(in-package "ACL2")
(include-book "arithmetic-5/top" :dir :system)

(defthm rfix-rationalp
  (implies
   (rationalp x)
   (equal (rfix x) x)))

(defthm rationalp-+-fwd
  (implies
   (and
    (rationalp x)
    (rationalp y))
   (rationalp (+ x y)))
  :rule-classes ((:forward-chaining :trigger-terms ((binary-+ x y)))))

(defthm rationalp-*-fwd
  (implies
   (and
    (rationalp x)
    (rationalp y))
   (rationalp (* x y)))
  :rule-classes ((:forward-chaining :trigger-terms ((binary-* x y)))))

(in-theory (disable rfix))

(defun add-list (list)
  (declare (type t list))
  (if (not (consp list)) 0
    (+ (rfix (car list)) (add-list (cdr list)))))

(defun mul-list (list)
  (declare (type t list))
  (if (not (consp list)) 1
    (* (rfix (car list)) (add-list (cdr list)))))

(defun lte (x y)
  (declare (type t x y))
  (implies (not y) (not x)))

(defun gte (x y)
  (declare (type t x y))
  (implies y x))

(defun max-list (list)
  (declare (type t list))
  (if (not (consp list)) nil
    (or (car list) (max-list (cdr list)))))

(defun min-list (list)
  (declare (type t list))
  (if (not (consp list)) t
    (and (car list) (min-list (cdr list)))))

#+joe
(defun ith (n list)
  (declare (type t n list))
  (if (not (consp list)) nil
    (let ((n (nfix n)))
      (if (zp n) (car list)
        (ith (1- n) (cdr list))))))

(defun getval (name default ctx)
  (declare (type t name ctx))
  (if (not (consp ctx)) default
    (let ((entry (car ctx)))
      (if (not (consp entry)) (getval name default (cdr ctx))
        (let ((key (car entry)))
          (if (equal name key) (cdr entry)
            (getval name default (cdr ctx))))))))

(defthm open-getval-on-cons
  (equal (getval name default (cons entry res))
         (let ((ctx (cons entry res)))
           (let ((entry (car ctx)))
             (if (not (consp entry)) (getval name default (cdr ctx))
               (let ((key (car entry)))
                 (if (equal name key) (cdr entry)
                   (getval name default (cdr ctx)))))))))

(in-theory (disable getval))

(defund any (x) (declare (type t x)) x)
(in-theory (disable (:type-prescription any)))

(encapsulate
    ()

  (set-tau-auto-mode nil)

  (defun ev-expr-p (x)
    (declare (type t x)
             (ignore x))
    t)

  (defthmd ev-expr-p-is-true
    (ev-expr-p x))

  (in-theory (disable ev-expr-p (:type-prescription ev-expr-p)))
  (set-tau-auto-mode t)  

  )

(defun ev-expr-listp (x)
  (declare (type t x))
  (if (not (consp x)) t
    (and (ev-expr-p (car x))
         (ev-expr-listp (cdr x)))))

(defthmd ev-expr-listp-is-true
  (ev-expr-listp x)
  :hints (("Goal" :in-theory (enable ev-expr-p-is-true))))

(local (in-theory (enable ev-expr-p-is-true ev-expr-listp-is-true)))

(defun not-list (x)
  (declare (type t x))
  (if (not (consp x)) nil
    (cons (not (car x))
          (not-list (cdr x)))))

(mutual-recursion

 (defun evAlt-list (list env)
   (declare (xargs :guard (ev-expr-listp list) :measure (acl2-count list)))
   (if (not (consp list)) nil
     (cons (evAlt (car list) env)
           (evAlt-list (cdr list) env))))
 
 (defun evAlt (expr env)
   (declare (xargs :guard (ev-expr-p expr) :measure (acl2-count expr)))
   (case-match expr
     (('= x y)
      (let ((x (evAlt x env))
            (y (evAlt y env)))
        (equal (rfix x) (rfix y))))
     (('!= x y)
      (let ((x (evAlt x env))
            (y (evAlt y env)))
        (not (equal (rfix x) (rfix y)))))
     (('< x y)
      (let ((x (evAlt x env))
            (y (evAlt y env)))
        (< (rfix x) (rfix y))))
     (('<= x y)
      (let ((x (evAlt x env))
            (y (evAlt y env)))
        (<= (rfix x) (rfix y))))
     (('> x y)
      (let ((x (evAlt x env))
            (y (evAlt y env)))
        (> (rfix x) (rfix y))))
     (('>= x y)
      (let ((x (evAlt x env))
            (y (evAlt y env)))
        (>= (rfix x) (rfix y))))
     (('lte x y)
      (let ((x (evAlt x env))
            (y (evAlt y env)))
        (lte x y)))
     (('gte x y)
      (let ((x (evAlt x env))
            (y (evAlt y env)))
        (gte x y)))
     (('max . y)
      (max-list (evAlt-list y env)))
     (('min . y)
      (min-list (evAlt-list y env)))
     (('+ . y)
      (add-list (evAlt-list y env)))
     (('and . y)
      (and-list (evAlt-list y env)))
     (('or . y)
      (or-list (evAlt-list y env)))
     (('* . y)
      (mul-list (evalt-list y env)))
     (('- x)
      (- (rfix (evAlt x env))))
     (('not x)
      (not (evAlt x env)))
     (('id n cex)
      (getval n cex env))
     (('lit val)
      val)
     (('tag & expr)
      (evAlt expr env))
     (& (any expr))))

 )

(mutual-recursion

 (defun evcex-list (list)
   (declare (xargs :guard (ev-expr-listp list) :measure (acl2-count list)))
   (if (not (consp list)) nil
     (cons (evcex (car list))
           (evcex-list (cdr list)))))
 
 (defun evcex (expr)
   (declare (xargs :guard (ev-expr-p expr) :measure (acl2-count expr)))
   (case-match expr
     (('= x y)
      (let ((x (evcex x))
            (y (evcex y)))
        (equal (rfix x) (rfix y))))
     (('!= x y)
      (let ((x (evcex x))
            (y (evcex y)))
        (not (equal (rfix x) (rfix y)))))
     (('< x y)
      (let ((x (evcex x))
            (y (evcex y)))
        (< (rfix x) (rfix y))))
     (('<= x y)
      (let ((x (evcex x))
            (y (evcex y)))
        (<= (rfix x) (rfix y))))
     (('> x y)
      (let ((x (evcex x))
            (y (evcex y)))
        (> (rfix x) (rfix y))))
     (('>= x y)
      (let ((x (evcex x))
            (y (evcex y)))
        (>= (rfix x) (rfix y))))
     (('lte x y)
      (let ((x (evcex x))
            (y (evcex y)))
        (lte x y)))
     (('gte x y)
      (let ((x (evcex x))
            (y (evcex y)))
        (gte x y)))
     (('max . y)
      (max-list (evcex-list y)))
     (('min . y)
      (min-list (evcex-list y)))
     (('+ . y)
      (add-list (evcex-list y)))
     (('and . y)
      (and-list (evcex-list y)))
     (('or . y)
      (or-list (evcex-list y)))
     (('* . y)
      (mul-list (evcex-list y)))
     (('- x)
      (- (rfix (evcex x))))
     (('not x)
      (not (evcex x)))
     (('id & cex)
      cex)
     (('lit val)
      val)
     (('tag & expr)
      (evcex expr))
     (& (any expr))))

 )

(defthm max-list-reduction
  (iff (max-list list)
       (or-list list)))

(defthm min-list-reduction
  (iff (min-list list)
       (and-list list)))

(defthm or-list-to-and-list
  (iff (or-list list)
       (not (and-list (not-list list)))))

(defthm evcex-list-append
  (equal (evcex-list (append x y))
         (append (evcex-list x)
                 (evcex-list y))))

(defthm evalt-list-append
  (equal (evalt-list (append x y) env)
         (append (evalt-list x env)
                 (evalt-list y env))))

(defthm not-list-append
  (equal (not-list (append x y))
         (append (not-list x)
                 (not-list y))))

(defthm and-list-append
  (equal (and-list (append x y))
         (and (and-list x)
              (and-list y))))

(defun bool-equiv-list (x y)
  (declare (type t x y))
  (if (and (consp x) (consp y))
      (and (iff (car x) (car y))
           (bool-equiv-list (cdr x) (cdr y)))
    (and (not (consp x)) (not (consp y)))))

(defequiv bool-equiv-list)
(defcong bool-equiv-list bool-equiv-list (not-list x) 1)
(defcong bool-equiv-list iff (and-list x) 1)

(defevaluator ev-ev ev-ev-list
  ((evalt arg any)
   (evcex arg)
   (if x y z)
   ))

(defun meta-and-evalt (args any)
  (if (consp args)
      `(if (evalt (quote ,(car args)) ,any)
           ,(meta-and-evalt (cdr args) any)
         (quote nil))
    `(quote t)))

(defthm ev-ev-meta-and-evalt
  (iff (ev-ev (meta-and-evalt expr any) env)
       (and-list (evalt-list expr (ev-ev any env)))))

(defun meta-and-evcex (args)
  (if (consp args)
      `(if (evcex (quote ,(car args)))
           ,(meta-and-evcex (cdr args))
         (quote nil))
    `(quote t)))

(defthm ev-ev-meta-and-evcex
  (iff (ev-ev (meta-and-evcex expr) env)
       (and-list (evcex-list expr))))

(defun meta-evx (term)
  (case-match term
   (('evalt ('quote body) any)
    (case-match body
      (('and . args)
       (meta-and-evalt args any))
      (& term)))
   (('evcex ('quote body))
    (case-match body
      (('and . args)
       (meta-and-evcex args))
      (& term)))
   (& term)))

(defthm *meta*-ev-ev-meta
  (iff (ev-ev term env)
       (ev-ev (meta-evx term) env))
  :rule-classes ((:meta :trigger-fns (evalt evcex))))


