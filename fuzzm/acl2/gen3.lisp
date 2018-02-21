;; 
;; Copyright (C) 2017, Rockwell Collins
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;; 
;; 
(in-package "ACL2")
(include-book "feature")

(def::und or-top (x y)
  (declare (xargs :signature ((top-p top-p) top-p)))
  (not-top (and-top (not-top x) (not-top y))))

(def::und or-top-list (list)
  (declare (xargs :signature ((top-listp) top-p)))
  (not-top (and-top-list (not-top-list list))))

(def::und max-top-list (list)
  (declare (xargs :signature ((top-listp) top-p)))
  (or-top-list list))

(def::und min-top-list (list)
  (declare (xargs :signature ((top-listp) top-p)))
  (and-top-list list))

(def::und implies-top (x y)
  (declare (xargs :signature ((top-p top-p) top-p)))
  (or-top (not-top x) y))

(def::und lte-top (x y)
  (declare (xargs :signature ((top-p top-p) top-p)))
  (implies-top (not-top y) (not-top x)))

(def::und gte-top (x y)
  (declare (xargs :signature ((top-p top-p) top-p)))
  (implies-top y x))

(defun alt-top-p (lst x)
  (declare (type t lst x))
  (if lst (top-listp x) 
    (top-p x)))

(defun alt-boolean-expr-p (lst x)
  (declare (type t lst x))
  (if lst (boolean-expr-listp x)
    (boolean-expr-p x)))

(defmacro gen-expr-list-macro (list)
  `(gen-expr-rec t ,list))

(defmacro gen-expr-macro (x)
  `(gen-expr-rec nil ,x))

(defthmd top-listp-from-alt-top-p
  (implies
   (alt-top-p t x)
   (top-listp x)))

(defthmd top-p-from-alt-top-p
  (implies
   (alt-top-p nil x)
   (top-p x)))

(def::un gen-expr-rec (lst expr)
  (declare (xargs :signature ((t (lambda (x) (alt-boolean-expr-p lst x))) (lambda (x) (alt-top-p lst x)))
                  :signature-hints ((and stable-under-simplificationp
                                         '(:in-theory (enable variable-name-p boolean-term-p))))
                  :guard-hints (("Goal" :in-theory (e/d (top-listp-from-alt-top-p top-p-from-alt-top-p) (alt-top-p alt-boolean-expr-p)))
                                (and stable-under-simplificationp
                                     '(:in-theory (enable variable-name-p boolean-term-p))))))
  (if lst
      (if (not (consp expr)) nil
        (cons (gen-expr-macro (car expr))
              (gen-expr-list-macro (cdr expr))))
    (case-match expr
      (('= & &)  (top-poly-only (tag t) (poly (tag t) expr)))
      (('!= & &) (top-poly-only (tag t) (poly (tag t) expr)))
      (('< & &)  (top-poly-only (tag t) (poly (tag t) expr)))
      (('<= & &) (top-poly-only (tag t) (poly (tag t) expr)))
      (('> & &)  (top-poly-only (tag t) (poly (tag t) expr)))
      (('>= & &) (top-poly-only (tag t) (poly (tag t) expr)))
      (('lte x y)
       (let ((x (gen-expr-macro x))
             (y (gen-expr-macro y)))
         (lte-top x y)))
      (('gte x y)
       (let ((x (gen-expr-macro x))
             (y (gen-expr-macro y)))
         (gte-top x y)))
      (('max . y)
       (max-top-list (gen-expr-list-macro y)))
      (('min . y)
       (min-top-list (gen-expr-list-macro y)))
      (('and . y)
       (and-top-list (gen-expr-list-macro y)))
      (('or . y)
       (or-top-list (gen-expr-list-macro y)))
      (('not x)
       (not-top (gen-expr-macro x)))
      (('id & &) (top-bool-only (tag t) (singleton! (tag t) (clause (tag t) (list expr)))))
      (('lit val)  (if val (true-top) (false-top)))
      (('tag & z) (gen-expr-macro z))
      (& (false-top)))))
 
(def::un gen-expr-list (list)
  (declare (xargs :signature ((boolean-expr-listp) top-listp)
                  :signature-hints (("Goal" :in-theory (e/d (top-listp-from-alt-top-p top-p-from-alt-top-p) (alt-top-p))))))
  (gen-expr-list-macro list))

(def::un gen-expr (x)
  (declare (xargs :signature ((boolean-expr-p) top-p)
                  :signature-hints (("Goal" :in-theory (e/d (top-listp-from-alt-top-p top-p-from-alt-top-p) (alt-top-p))))))
  (gen-expr-macro x))

(defthmd gen-expr-list-rec-abstraction
  (implies
   lst
   (equal (gen-expr-rec lst expr)
          (gen-expr-list expr))))

(defthmd gen-expr-rec-abstraction
  (equal (gen-expr-macro expr)
         (gen-expr expr)))

(defthm gen-expr-list-definition
  (equal (gen-expr-list expr)
         (if (not (consp expr)) nil
           (cons (gen-expr (car expr))
                 (gen-expr-list (cdr expr)))))
  :rule-classes ((:definition :controller-alist ((gen-expr-list t)))))

(defthm gen-expr-definition
  (equal (gen-expr expr)
         (case-match expr
           (('= & &)  (top-poly-only (tag t) (poly (tag t) expr)))
           (('!= & &) (top-poly-only (tag t) (poly (tag t) expr)))
           (('< & &)  (top-poly-only (tag t) (poly (tag t) expr)))
           (('<= & &) (top-poly-only (tag t) (poly (tag t) expr)))
           (('> & &)  (top-poly-only (tag t) (poly (tag t) expr)))
           (('>= & &) (top-poly-only (tag t) (poly (tag t) expr)))
           (('lte x y)
            (let ((x (gen-expr x))
                  (y (gen-expr y)))
              (lte-top x y)))
           (('gte x y)
            (let ((x (gen-expr x))
                  (y (gen-expr y)))
              (gte-top x y)))
           (('max . y)
            (max-top-list (gen-expr-list y)))
           (('min . y)
            (min-top-list (gen-expr-list y)))
           (('and . y)
            (and-top-list (gen-expr-list y)))
           (('or . y)
            (or-top-list (gen-expr-list y)))
           (('not x)
            (not-top (gen-expr x)))
           (('id & &) (top-bool-only (tag t) (singleton! (tag t) (clause (tag t) (list expr)))))
           (('lit val)  (if val (true-top) (false-top)))
           (('tag & z) (gen-expr z))
           (& (false-top))))
  :rule-classes ((:definition :controller-alist ((gen-expr t)))))

(in-theory (disable (:definition gen-expr-rec)))
(in-theory (disable gen-expr gen-expr-list))
(in-theory (enable gen-expr-list-rec-abstraction gen-expr-rec-abstraction))

(defthm atom-p-singleton!
  (implies
   (and (tag-p tag) (clause-p clause))
   (iff (atom-p (singleton! tag clause))
        (and (consp (clause-body clause))
             (null (cdr (clause-body clause))))))
  :hints (("Goal" :in-theory (enable singleton! get-singleton atom-p singleton-p))))

(defthm get-atom-singleton!
  (implies
   (and (tag-p tag) (clause-p clause))
   (equal (get-atom (singleton! tag clause))
          (car (clause-body clause))))
  :hints (("Goal" :in-theory (enable singleton! get-singleton get-atom atom-p singleton-p))))
  
(defun map-evcex (x y)
  (if (and (consp x) (consp y))
      (and (iff (evcex (top-gen (car x)))
                (evcex (car y)))
           (map-evcex (cdr x) (cdr y)))
    (and (null x) (null y))))

(defthm map-evcex-implication
  (implies
   (map-evcex x y)
   (bool-equiv-list (evcex-list (top-gen-list x))
                    (evcex-list y))))

(in-theory (enable or-top-list or-top))
(in-theory (enable min-top-list max-top-list))
(in-theory (enable implies-top lte-top gte-top))

(in-theory (enable and-top-list))
(in-theory (disable add-list mul-list))
(in-theory (disable not-top))

(defthm evcex-gen-expr
  (and
   (implies
    (and lst (boolean-expr-listp expr))
    (map-evcex (gen-expr-list expr)
               expr))
   (implies
    (and (not lst) (boolean-expr-p expr))
    (iff (evcex (top-gen (gen-expr expr)))
         (evcex expr))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable boolean-term-p
                              variable-name-p)
           :induct (gen-expr-rec lst expr))))

;; #+joe
;; (gen-expr
;;  '(or (or (not (id x nil))
;;           (id y nil))
;;       (not
;;        (and (id z t)
;;             (not (id x t))))))

;; We could/should improve this.  I still think the right way may be
;; to mix abstractions.

;; The key is to ensure that we are using the right generalization
;; target at every point.  I think in order to do it correctly we will
;; need to have both generalizations available.  Remember: the +
;; generalization can always just be the cex.

;; (feature )
;; (both x- x+)

;; #+joe
;; (gen-expr
;;  '(or (and (not (id a t))
;;            (id b nil)
;;            (id c t))
;;       (and (not (id d nil))
;;            (not (id e nil))
;;            (id f t))
;;       (and (not (id g t))
;;            (id h nil)
;;            (id i t))))

