;; 
;; Copyright (C) 2017, Rockwell Collins
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;; 
;; 
(in-package "ACL2")

(include-book "doublecheck")
(include-book "coi/util/defun" :dir :system)

(defun beta (term)
  (declare (type (satisfies pseudo-termp) term))
  (if (lambda-expr-p term)
      (beta-reduce-lambda-expr term)
    term))

(defmacro def::and (fname &key (type-p 'nil) (xtype-p 'nil) (ytype-p 'nil) (gen '(lambda (x) x)) (both-p 'nil) (true 'nil) (false 'nil) (weak 'nil) (hints 'nil) (evcex 'evcex) (evalt 'evalt))
  (declare (xargs :guard (and (and (or type-p (and ytype-p xtype-p)) both-p)
                              (implies weak (not (iff true false))))))
  (let* ((ytype-p  (or type-p ytype-p))
         (xtype-p  (or type-p xtype-p))
         (inv1     (packn-pos `("INV1-" ,fname) fname))
         (inv2     (packn-pos `("INV2-" ,fname) fname))
         (inv2-T-  (packn-pos `("INV2-T-" ,fname) fname))
         (inv2-F-  (packn-pos `("INV2-F-" ,fname) fname))
         (both-p-fname (packn-pos `("BOTH-" ,fname) fname))
         (not-both-p-fname-1 (packn-pos `("NOT-BOTH-" ,fname "-1") fname))
         (not-both-p-fname-2 (packn-pos `("NOT-BOTH-" ,fname "-2") fname))
         (hints (and hints `(:hints ,hints)))
         )
    `(encapsulate
         ()

       (local (in-theory (enable ,fname)))

       ,(or (and (not weak) `(defthm ,inv1
                               (implies
                                (and
                                 (,xtype-p x)
                                 (,ytype-p y))
                                (iff ,(beta `(,evCex ,(beta `(,gen (,fname x y)))))
                                     (and (,evcex (,gen x))
                                          (,evcex (,gen y)))))
                               ,@hints))
            (and weak true `(defthm ,inv1
                              (implies
                               (and
                                (,xtype-p x)
                                (,ytype-p y)
                                (,evcex (,gen x))
                                (,evcex (,gen y)))
                               ,(beta `(,evcex ,(beta `(,gen (,fname x y))))))
                              ,@hints))
            (and weak false `(defthm ,inv1
                              (implies
                               (and
                                (,xtype-p x)
                                (,ytype-p y)
                                (not (,evcex (,gen x)))
                                (not (,evcex (,gen y))))
                               (not ,(beta `(,evcex ,(beta `(,gen (,fname x y)))))))
                              ,@hints))
            )

       (defthm ,inv2
         (implies
          (and
           (,both-p (,fname x y))
           (,xtype-p x)
           (,ytype-p y))
          (iff ,(beta `(,evalt ,(beta `(,gen (,fname x y))) env))
               (and (,evalt (,gen x) env)
                    (,evalt (,gen y) env))))
         ,@hints)

       ,@(and true `((defthm ,inv2-T-
                       (implies
                        (and
                         (,xtype-p x)
                         (,ytype-p y)
                         (,evcex (,gen x))
                         (,evcex (,gen y))
                         (case-split (not (and (,evalt (,gen x) env)
                                               (,evalt (,gen y) env)))))
                        (not ,(beta `(,evalt ,(beta `(,gen (,fname x y))) env))))
                       ,@hints)))
                     
       ,@(and false `((defthm ,inv2-F-
                        (implies
                         (and
                          (,xtype-p x)
                          (,ytype-p y)
                          (not (,evcex (,gen y)))
                          (not (,evcex (,gen x)))
                          (case-split (,evalt (,gen x) env))
                          (case-split (,evalt (,gen y) env)))
                         ,(beta `(,evalt ,(beta `(,gen (,fname x y))) env)))
                        ,@hints)))

       (defthm ,both-p-fname
         (implies
          (and
           ,(beta `(,both-p (,fname x y)))
           (,xtype-p x)
           (,ytype-p y))
          (and ,(beta `(,both-p x))
               ,(beta `(,both-p y))))
         ,@hints
         :rule-classes (:forward-chaining))

       (defthm ,not-both-p-fname-1
         (implies
          (and
           (not ,(beta `(,both-p x)))
           (,xtype-p x)
           (,ytype-p y))
          (not ,(beta `(,both-p (,fname x y)))))
         ,@hints
         :rule-classes ((:forward-chaining :trigger-terms ((,fname x y)))
                        :rewrite :type-prescription))
       
       (defthm ,not-both-p-fname-2
         (implies
          (and
           (not ,(beta `(,both-p y)))
           (,xtype-p x)
           (,ytype-p y))
          (not ,(beta `(,both-p (,fname x y)))))
         ,@hints
         :rule-classes ((:forward-chaining :trigger-terms ((,fname x y)))
                        :rewrite :type-prescription))
       
       )))

;; -------------------------------------------------------------------

(defmacro boolean-expr-listp-macro (list)
  `(boolean-expr-p-rec t ,list))

(defmacro boolean-expr-p-macro (expr)
  `(boolean-expr-p-rec nil ,expr))

(defun boolean-expr-p-rec (lst expr)
  (declare (type t lst expr))
  (if lst
      (if (not (consp expr)) (null expr)
        (and (boolean-expr-p-macro (car expr))
             (boolean-expr-listp-macro (cdr expr))))
    (case-match expr
      (('= & &)  t)
      (('!= & &) t)
      (('< & &)  t)
      (('<= & &) t)
      (('> & &)  t)
      (('>= & &) t)
      (('lte x y)
       (let ((x (boolean-expr-p-macro x))
             (y (boolean-expr-p-macro y)))
         (and x y)))
      (('gte x y)
       (let ((x (boolean-expr-p-macro x))
             (y (boolean-expr-p-macro y)))
         (and x y)))
      (('max . y)
       (boolean-expr-listp-macro y))
      (('min . y)
       (boolean-expr-listp-macro y))
      (('and . y)
       (boolean-expr-listp-macro y))
      (('or . y)
       (boolean-expr-listp-macro y))
      (('not x)
       (boolean-expr-p-macro x))
      (('id & cex) (booleanp cex))
      (('lit val)  (booleanp val))
      (('tag & expr) (boolean-expr-p-macro expr))
      (& nil))))

(defund boolean-expr-listp (list)
  (declare (type t list))
  (boolean-expr-listp-macro list))

(defund boolean-expr-p (expr)
  (declare (type t expr))
  (boolean-expr-p-macro expr))

(defthm boolean-expr-p-implies-ev-expr-p
  (implies
   (boolean-expr-p expr)
   (ev-expr-p expr))
  :hints (("Goal" :in-theory (enable ev-expr-p-is-true)))
  :rule-classes (:forward-chaining))

(defthm boolean-expr-listp-implies-ev-expr-listp
  (implies
   (boolean-expr-listp expr)
   (ev-expr-listp expr))
  :hints (("Goal" :in-theory (enable ev-expr-listp-is-true)))
  :rule-classes (:forward-chaining))

(defthm boolean-expr-listp-definition
  (equal (boolean-expr-listp expr)
         (if (not (consp expr)) (null expr)
           (and (boolean-expr-p (car expr))
                (boolean-expr-listp (cdr expr)))))
  :rule-classes ((:definition :controller-alist ((boolean-expr-listp t))))
  :hints (("Goal" :in-theory (enable boolean-expr-listp boolean-expr-p))))

(defthm boolean-expr-p-definition
  (equal (boolean-expr-p expr)
         (case-match expr
           (('= & &)  t)
           (('!= & &) t)
           (('< & &)  t)
           (('<= & &) t)
           (('> & &)  t)
           (('>= & &) t)
           (('lte x y)
            (let ((x (boolean-expr-p x))
                  (y (boolean-expr-p y)))
              (and x y)))
           (('gte x y)
            (let ((x (boolean-expr-p x))
                  (y (boolean-expr-p y)))
              (and x y)))
           (('max . y)
            (boolean-expr-listp y))
           (('min . y)
            (boolean-expr-listp y))
           (('and . y)
            (boolean-expr-listp y))
           (('or . y)
            (boolean-expr-listp y))
           (('not x)
            (boolean-expr-p x))
           (('id & cex) (booleanp cex))
           (('lit val)  (booleanp val))
           (('tag & expr) (boolean-expr-p expr))
           (& nil)))
  :rule-classes ((:definition :controller-alist ((boolean-expr-p t))))
  :hints (("Goal" :in-theory (enable boolean-expr-listp boolean-expr-p))))

(defthm boolean-p-rec-definition
  (equal (boolean-expr-p-rec lst expr)
         (if lst (boolean-expr-listp expr)
           (boolean-expr-p expr)))
  :rule-classes (:definition)
  :hints (("Goal" :in-theory (enable  boolean-expr-listp boolean-expr-p))))

(in-theory (disable boolean-expr-p-rec))

(defthm boolean-expr-p-rec-implication-1
  (implies
   (and
    (boolean-expr-p-rec lst expr)
    (not lst))
   (boolean-expr-p expr))
  :rule-classes (:forward-chaining))

(defthm boolean-expr-p-rec-implication-2
  (implies
   (and
    (boolean-expr-p-rec lst expr)
    lst)
   (boolean-expr-listp expr))
  :rule-classes (:forward-chaining))

(defthm implies-boolean-expr-p-rec-1
  (implies
   (boolean-expr-p expr)
   (boolean-expr-p-rec nil expr))
  :rule-classes (:forward-chaining))

(defthm implies-boolean-expr-p-rec-2
  (implies
   (boolean-expr-listp expr)
   (boolean-expr-p-rec t expr))
  :rule-classes (:forward-chaining))

;; -------------------------------------------------------------------

(defun not-expr-p (x)
  (declare (type t x))
  (case-match x
    (('not &) t)
    (& nil)))

(def::und not-expr (x)
  (declare (xargs :signature ((boolean-expr-p) boolean-expr-p)))
  (case-match x
    (('not a) a)
    (('lit x) `(lit ,(not x)))
    (& `(not ,x))))

(defthm evAlt-not-expr
  (iff (evAlt (not-expr x) env)
       (not (evAlt x env)))
  :hints (("Goal" :in-theory (enable not-expr))))

(defthm evCex-not-expr
  (iff (evCex (not-expr x))
       (not (evCex x)))
  :hints (("Goal" :in-theory (enable not-expr))))

;; -------------------------------------------------------------------

(def::un not-expr-list (list)
  (declare (xargs :signature ((boolean-expr-listp) boolean-expr-listp)))
  (if (not (consp list)) nil
    (cons (not-expr (car list))
          (not-expr-list (cdr list)))))

(defthm not-expr-list-append
  (equal (not-expr-list (append x y))
         (append (not-expr-list x)
                 (not-expr-list y))))

(defthm and-list-evcex-list-not-list
  (implies
   (boolean-expr-listp list)
   (bool-equiv-list (evcex-list (not-expr-list list))
                    (not-list (evcex-list list)))))

(defthm and-list-evalt-list-not-list
  (implies
   (boolean-expr-listp list)
   (bool-equiv-list (evalt-list (not-expr-list list) env)
                    (not-list (evalt-list list env)))))

;; -------------------------------------------------------------------

(defund variable-name-p (expr)
  (declare (type t expr))
  (case-match expr
    (('id & v) (booleanp v))
    (& nil)))

(defthm variable-name-p-car
  (implies
   (variable-name-p x)
   (equal (car x) 'id))
  :hints (("Goal" :in-theory (enable variable-name-p)))
  :rule-classes (:forward-chaining))

(defthm variable-name-p-implies-boolean-expr-p
  (implies
   (variable-name-p expr)
   (boolean-expr-p expr))
  :hints (("Goal" :in-theory (enable variable-name-p)))
  :rule-classes :forward-chaining)

(defun boolean-term-p (x)
  (declare (type t x))
  (case-match x
    (('not a) (variable-name-p a))
    (& (variable-name-p x))))

(defthm boolean-term-p-implies-boolean-expr-p
  (implies
   (boolean-term-p expr)
   (boolean-expr-p expr))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable variable-name-p))))

(defthm boolean-leaves-arent-negated
  (implies
   (variable-name-p x)
   (not (equal (car x) 'not)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable variable-name-p))))

(def::signature not-expr (boolean-term-p) boolean-term-p
  :hints (("Goal" :in-theory (enable not-expr))))

(in-theory (disable boolean-term-p))

;; -------------------------------------------------------------------

(defun boolean-term-listp (args)
  (declare (type t args))
  (if (not (consp args)) (null args)
    (and (boolean-term-p (car args))
         (boolean-term-listp (cdr args)))))

(defthm boolean-term-listp-implies-true-listp
  (implies
   (boolean-term-listp x)
   (true-listp x))
  :rule-classes :forward-chaining)

(def::signature append (boolean-term-listp boolean-term-listp) boolean-term-listp)

(defthm boolean-term-listp-implies-boolean-expr-listp
  (implies
   (boolean-term-listp args)
   (boolean-expr-listp args))
  :rule-classes :forward-chaining)

(defthm open-boolean-term-listp
  (implies
   (and
    (boolean-term-listp list)
    (consp list))
   (and (boolean-term-p (car list))
        (boolean-term-listp (cdr list))))
  :rule-classes (:rewrite :forward-chaining))

(def::signature not-expr-list (boolean-term-listp) boolean-term-listp)

;; -------------------------------------------------------------------

(defund tag-p (x)
  (declare (type t x))
  (symbolp x))

(defund feature-p (x)
  (declare (type (satisfies tag-p) x))
  (equal x :feature))

(def::und tag (x)
  (declare (xargs :signature ((booleanp) tag-p)))
  (if x :feature :artifact))

(defthm feature-p-tag
  (iff (feature-p (tag x)) x)
  :hints (("Goal" :in-theory (enable tag feature-p))))

(in-theory (disable (tag)))

;; -------------------------------------------------------------------

(defun clause-p (x)
  (declare (type t x))
  (case-match x
    (('tag tag ('or . args))
     (and (tag-p tag)
          (boolean-term-listp args)))
    (& nil)))

(defthm clause-p-implies-boolean-expr-p
  (implies
   (clause-p x)
   (boolean-expr-p x))
  :rule-classes (:forward-chaining))

(def::und clause (tag args)
  (declare (xargs :signature ((tag-p boolean-term-listp) clause-p)))
  `(tag ,tag (or ,@args)))

(def::un clause-body (clause)
  (declare (xargs :signature ((clause-p) boolean-term-listp)))
  (case-match clause
    (('tag & ('or . args)) args)
    (& nil)))

(def::un clause-tag (clause)
  (declare (xargs :signature ((clause-p) tag-p)))
  (case-match clause
    (('tag tag ('or . &)) tag)
    (& nil)))

(def::un clause-feature-p (x)
  (declare (xargs :signature ((clause-p) booleanp)))
  (feature-p (clause-tag x)))

(defthmd evcex-clause-p
  (implies
   (clause-p x)
   (iff (evcex x)
        (or-list (evcex-list (clause-body x))))))

(defthmd evalt-clause-p
  (implies
   (clause-p x)
   (iff (evalt x env)
        (or-list (evalt-list (clause-body x) env)))))

(defthm clause-body-clause
  (equal (clause-body (clause tag args))
         args)
  :hints (("Goal" :in-theory (enable clause))))

(defthm clause-tag-clause
  (equal (clause-tag (clause tag args))
         tag)
  :hints (("Goal" :in-theory (enable clause))))

(defthm clause-feature-clause
  (equal (clause-feature-p (clause tag args))
         (feature-p tag))
  :hints (("Goal" :in-theory (enable clause))))

(defthm feature-clause-tag
  (iff (feature-p (clause-tag x))
       (clause-feature-p x)))

(in-theory (disable clause-p clause-body clause-tag clause-feature-p))

(theory-invariant
 (incompatible
  (:definition clause-feature-p)
  (:rewrite feature-clause-tag)))

(defthm evcex-clause
  (implies
   (force (and (tag-p tag) (boolean-term-listp body)))
   (iff (evcex (clause tag body))
        (or-list (evcex-list body))))
  :hints (("Goal" :in-theory (enable evcex-clause-p))))

(defthm evalt-clause
  (implies
   (force (and (tag-p tag) (boolean-term-listp body)))
   (iff (evalt (clause tag body) env)
        (or-list (evalt-list body env))))
  :hints (("Goal" :in-theory (enable evalt-clause-p))))

;; -------------------------------------------------------------------

(defun clause-listp (x)
  (declare (type t x))
  (if (not (consp x)) (null x)
    (and (clause-p (car x))
         (clause-listp (cdr x)))))

(def::signature append (clause-listp clause-listp) clause-listp)

(defthm clause-listp-implies-boolean-expr-listp
  (implies
   (clause-listp x)
   (boolean-expr-listp x))
  :rule-classes :forward-chaining)

(def::un clause-feature-listp (x)
  (declare (xargs :signature ((clause-listp) booleanp)))
  (if (not (consp x)) t
    (and (clause-feature-p (car x))
         (clause-feature-listp (cdr x)))))

(defthm open-clause-listp
  (implies
   (and
    (clause-listp list)
    (consp list))
   (and (clause-p (car list))
        (clause-listp (cdr list))))
  :rule-classes (:rewrite :forward-chaining))

(def::signature append (clause-feature-listp clause-feature-listp) clause-feature-listp)

;; -------------------------------------------------------------------

(def::un clausify-term-list (tag x)
  (declare (xargs :signature ((tag-p boolean-term-listp) clause-listp)))
  (if (not (consp x)) nil
    (cons (clause tag (list (car x)))
          (clausify-term-list tag (cdr x)))))

(defthm clauseify-term-list-append
  (equal (clausify-term-list tag (append x y))
         (append (clausify-term-list tag x)
                 (clausify-term-list tag y))))

(defthm evcex-list-clausify-term-list
  (implies
   (and (tag-p tag) (boolean-term-listp list))
   (bool-equiv-list (evcex-list (clausify-term-list tag list))
                    (evcex-list list)))
  :hints (("Goal" :in-theory (enable evcex-clause))))

(defthm evalt-list-clausify-term-list
  (implies
   (and (tag-p tag) (boolean-term-listp list))
   (bool-equiv-list (evalt-list (clausify-term-list tag list) env)
                    (evalt-list list env)))
  :hints (("Goal" :in-theory (enable evalt-clause))))

;; -------------------------------------------------------------------

(defun cnf-p (x)
  (declare (type t x))
  (case-match x
    (('tag z ('and . args))
     (and (tag-p z) (clause-listp args)
          (implies (feature-p z) (clause-feature-listp args))))
    (& nil)))

(def::und cnf-body (x)
  (declare (xargs :signature ((cnf-p) clause-listp)))
  (case-match x
    (('tag & ('and . args)) args)
    (& nil)))

(def::und cnf-tag (x)
  (declare (xargs :signature ((cnf-p) tag-p)))
  (case-match x
    (('tag tag ('and . &)) tag)
    (& nil)))

(def::un cnf-feature-p (x)
  (declare (xargs :signature ((cnf-p) booleanp)))
  (feature-p (cnf-tag x)))

(defthmd evcex-cnf-p
  (implies
   (cnf-p x)
   (iff (evcex x)
        (and-list (evcex-list (cnf-body x)))))
  :hints (("Goal" :in-theory (enable cnf-body))))

(defthmd evalt-cnf-p
  (implies
   (cnf-p cnf)
   (iff (evalt cnf env)
        (and-list (evalt-list (cnf-body cnf) env))))
  :hints (("Goal" :in-theory (enable cnf-body cnf-p))))

(def::und cnf (tag list)
  (declare (xargs :signature ((tag-p clause-listp) cnf-p)))
  `(tag ,(if (clause-feature-listp list) tag (tag nil)) (and ,@list)))

(defthm cnf-body-cnf
  (equal (cnf-body (cnf tag list))
         list)
  :hints (("Goal" :in-theory (enable cnf cnf-body))))

(defthm cnf-tag-cnf
  (equal (cnf-tag (cnf tag list))
         (if (clause-feature-listp list) tag (tag nil)))
  :hints (("Goal" :in-theory (enable cnf cnf-tag))))

(defthm cnf-feature-cnf
  (equal (cnf-feature-p (cnf tag list))
         (feature-p (if (clause-feature-listp list) tag (tag nil))))
  :hints (("Goal" :in-theory (enable cnf cnf-tag))))

(def::un cnf! (list)
  (declare (xargs :signature ((clause-listp) cnf-p)))
  (cnf (tag (clause-feature-listp list)) list))

(defthm cnf-p-implies-boolean-expr-p
  (implies
   (cnf-p x)
   (boolean-expr-p x))
  :rule-classes :forward-chaining)

(defthm cnf-p-implies-clause-feature-listp
  (implies
   (and
    (cnf-p x)
    (cnf-feature-p x))
   (clause-feature-listp (cnf-body x)))
  :hints (("Goal" :in-theory (enable cnf-tag cnf-body)))
  :rule-classes (:forward-chaining))

(defthm cnf-p-cnf
  (iff (cnf-p (cnf tag list))
       (let ((tag (if (clause-feature-listp list) tag (tag nil))))
         (and (tag-p tag)
              (clause-listp list)
              (implies
               (feature-p tag)
               (clause-feature-listp list)))))
  :hints (("Goal" :in-theory (enable cnf))))

(defthm not-not-expr-p-cnf
  (not (not-expr-p (cnf tag x)))
  :hints (("Goal" :in-theory (enable cnf not-expr-p))))

(defthm feature-p-cnf-tag
  (iff (feature-p (cnf-tag x))
       (cnf-feature-p x)))

(in-theory (disable cnf-feature-p cnf-p))

(theory-invariant
 (incompatible (:rewrite feature-p-cnf-tag)
               (:definition cnf-feature-p)))

(def::un defeature-cnf (x)
  (declare (xargs :signature ((cnf-p) cnf-p)))
  (cnf (tag nil) (cnf-body x)))

(defthm evcex-cnf
  (implies
   (force (and (tag-p tag) (clause-listp list)))
   (iff (evcex (cnf tag list))
        (and-list (evcex-list list))))
  :hints (("Goal" :in-theory (enable evcex-cnf-p))))

(defthm evalt-cnf
  (implies
   (force (and (tag-p tag) (clause-listp list)))
   (iff (evalt (cnf tag list) env)
        (and-list (evalt-list list env))))
  :hints (("Goal" :in-theory (enable evalt-cnf-p))))

;; -------------------------------------------------------------------

(encapsulate
    ()

(defun nf-p (x)
  (declare (type t x))
  (case-match x
    (('not a) (cnf-p a))
    (&        (cnf-p x))))

(local (in-theory (enable cnf-p)))

(def::un nf (cnf)
  (declare (xargs :signature ((cnf-p) nf-p)))
  cnf)

(def::signature not-expr (nf-p) nf-p
  :hints (("Goal" :in-theory (enable cnf-p not-expr))))

(defthm nf-p-implies-boolean-expr-p
  (implies
   (nf-p x)
   (boolean-expr-p x))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable cnf-p))))

(def::und nf-cnf (x)
  (declare (xargs :signature ((nf-p) cnf-p)))
  (case-match x
    (('not cnf) cnf)
    (&  x)))

(defthm nf-cnf-nf
  (implies
   (cnf-p x)
   (equal (nf-cnf (nf x))
          x))
  :hints (("Goal" :in-theory (enable nf-cnf))))

(defthm nf-cnf-not-expr
  (implies
   (nf-p x)
   (equal (nf-cnf (not-expr x))
          (nf-cnf x)))
  :hints (("Goal" :in-theory (enable nf-p not-expr nf-cnf))))

(defthmd evcex-nf-p
  (implies
   (nf-p x)
   (iff (evcex x)
        (if (not-expr-p x)
            (not (evcex (nf-cnf x)))
          (evcex (nf-cnf x)))))
  :hints (("Goal" :in-theory (enable cnf-p cnf-body nf-cnf))))

(defthmd evalt-nf-p
  (implies
   (nf-p x)
   (iff (evalt x env)
        (if (not-expr-p x) (not (evalt (nf-cnf x) env))
          (evalt (nf-cnf x) env))))
  :hints (("Goal" :in-theory (enable cnf-p cnf-body nf-cnf))))

(def::un nf-clause-list (x)
  (declare (xargs :signature ((nf-p) clause-listp)))
  (cnf-body (nf-cnf x)))

(def::un bool-feature-p (x)
  (declare (xargs :signature ((nf-p) booleanp)))
  (cnf-feature-p (nf-cnf x)))

(def::un nf-tag (x)
  (declare (xargs :signature ((nf-p) tag-p)))
  (cnf-tag (nf-cnf x)))

(defthm nf-tag-nf
  (implies
   (cnf-p cnf)
   (equal (nf-tag (nf cnf))
          (cnf-tag cnf)))
  :hints (("Goal" :in-theory (enable cnf-p nf-cnf cnf-tag))))

;; (def::un defeature-bool (x)
;;   (declare (xargs :signature ((nf-p) nf-p)))
;;   (if (not-expr-p x)
;;       (not-expr (nf (defeature-cnf (nf-cnf x))))
;;     (nf (defeature-cnf (nf-cnf x)))))

(defthm not-expr-p-nf
  (implies
   (cnf-p x)
   (not (not-expr-p (nf x))))
  :hints (("Goal" :in-theory (enable cnf-p not-expr-p nf))))

(defthm not-expr-p-not-expr
  (implies
   (nf-p x)
   (iff (not-expr-p (not-expr x))
        (not (not-expr-p x))))
  :hints (("Goal" :in-theory (enable not-expr not-expr-p cnf-p nf-p))))

(defthm bool-feature-p-not-expr
  (implies
   (nf-p x)
   (iff (bool-feature-p (not-expr x))
        (bool-feature-p x)))
  :hints (("Goal" :in-theory (enable nf-cnf not-expr))))

(defthm cnf-feature-nf-cnf
  (iff (cnf-feature-p (nf-cnf x))
       (bool-feature-p x)))

(in-theory (disable bool-feature-p not-expr-p))
(in-theory (disable nf nf-p))

)

(theory-invariant
 (incompatible
  (:definition bool-feature-p)
  (:rewrite cnf-feature-nf-cnf)))

(defthm bool-feature-nf
  (implies
   (cnf-p cnf)
   (iff (bool-feature-p (nf cnf))
        (cnf-feature-p cnf)))
  :hints (("Goal" :in-theory (e/d (bool-feature-p)
                                  (cnf-feature-nf-cnf)))))
(defthm evcex-nf
  (implies
   (force (cnf-p y))
   (iff (evcex (nf y))
        (evcex y)))
  :hints (("Goal" :in-theory (enable evcex-nf-p))))

(defthm evalt-nf
  (implies
   (force (cnf-p y))
   (iff (evalt (nf y) env)
        (evalt y env)))
  :hints (("Goal" :in-theory (enable evalt-nf-p))))

;; -------------------------------------------------------------------

(defun poly-p (x)
  (declare (type t x))
  (case-match x
    ((`tag x y) (and (tag-p x) (boolean-expr-p y)))
    (& nil)))

(defthm poly-p-implies-boolean-expr-p
  (implies
   (poly-p x)
   (boolean-expr-p x))
  :rule-classes (:forward-chaining))

(def::und poly (tag x)
  (declare (xargs :signature ((tag-p boolean-expr-p) poly-p)))
  `(tag ,tag ,x))

(def::und poly-expr (x)
  (declare (xargs :signature ((poly-p) boolean-expr-p)))
  (case-match x
    ((`tag & y) y)
    (& nil)))

(def::und poly-tag (x)
  (declare (xargs :signature ((poly-p) tag-p)))
  (case-match x
    ((`tag tag &) tag)
    (& nil)))

(defthm poly-tag-poly
  (equal (poly-tag (poly x y))
         x)
  :hints (("Goal" :in-theory (enable poly-tag poly))))

(defthm poly-expr-poly
  (equal (poly-expr (poly x y))
         y)
  :hints (("Goal" :in-theory (enable poly-expr poly))))

(def::un poly-feature-p (x)
  (declare (xargs :signature ((poly-p) booleanp)))
  (feature-p (poly-tag x)))

(defthmd evcex-poly-p
  (implies
   (poly-p x)
   (iff (evcex x)
        (evcex (poly-expr x))))
  :hints (("Goal" :in-theory (enable poly-expr))))

(defthmd evalt-poly-p
  (implies
   (poly-p x)
   (iff (evalt x env)
        (evalt (poly-expr x) env)))
  :hints (("Goal" :in-theory (enable poly-expr))))

(defthm feature-poly-tag
  (iff (feature-p (poly-tag x))
       (poly-feature-p x)))

(defthm poly-feature-p-poly
  (equal (poly-feature-p (poly tag x))
         (feature-p tag)))

(in-theory (disable poly-feature-p))
(in-theory (disable poly-p))

(theory-invariant
 (incompatible
  (:definition poly-feature-p)
  (:rewrite feature-poly-tag)))
  
(defthm evcex-poly
  (implies
   (and (tag-p tag) (boolean-expr-p expr))
   (iff (evcex (poly tag expr))
        (evcex expr)))
  :hints (("Goal" :in-theory (enable evcex-poly-p))))

(defthm evalt-poly
  (implies
   (and (tag-p tag) (boolean-expr-p expr))
   (iff (evalt (poly tag expr) env)
        (evalt expr env)))
  :hints (("Goal" :in-theory (enable evalt-poly-p))))

;; -------------------------------------------------------------------

(defun op-p (x)
  (declare (type t x))
  (or (equal x :and)
      (equal x :or)))

(def::un and-op-p (x)
  (declare (xargs :signature ((op-p) booleanp)))
  (equal x :and))

(defthm and-op-p-implication
  (implies
   (and-op-p x)
   (equal x :and))
  :rule-classes (:forward-chaining))

(defthm not-and-op-op-p
  (implies
   (and
    (op-p x)
    (not (and-op-p x)))
   (equal x :or))
  :rule-classes (:forward-chaining))

(in-theory (disable and-op-p))

(def::und not-op (op)
  (declare (xargs :signature ((op-p) op-p)))
  (if (and-op-p op) :or :and))

;; -------------------------------------------------------------------

(defun weak-top-p (x)
  (declare (type t x))
  (and (consp x)
       (op-p (car x))
       (consp (cdr x))
       (nf-p (cadr x))
       (consp (cddr x))
       (poly-p (caddr x))
       (consp (cdddr x))
       (tag-p (cadddr x))
       (null (cddddr x))))

(def::und top (tag op bool poly)
  (declare (xargs :signature ((tag-p op-p nf-p poly-p) weak-top-p)))
  (list op bool poly (if (and (poly-feature-p poly)
                              (bool-feature-p bool)) tag (tag nil))))

(defthm weak-top-p-top
  (iff (weak-top-p (top tag op bool poly))
       (and (op-p op)
            (nf-p bool)
            (poly-p poly)
            (if (and (poly-feature-p poly)
                     (bool-feature-p bool)) (tag-p tag) t)))
  :hints (("Goal" :in-theory (enable top))))

(def::un top! (op bool poly)
  (declare (xargs :signature ((op-p nf-p poly-p) weak-top-p)))
  (top (tag (and (poly-feature-p poly)
                 (bool-feature-p bool)))
       op bool poly))

(def::und top-op (x)
  (declare (xargs :signature ((weak-top-p) op-p)))
  (car x))

(def::und top-bool (x)
  (declare (xargs :signature ((weak-top-p) nf-p)))
  (cadr x))

(def::und top-poly (x)
  (declare (xargs :signature ((weak-top-p) poly-p)))
  (caddr x))

(def::und top-tag (x)
  (declare (xargs :signature ((weak-top-p) tag-p)))
  (cadddr x))

(defthm top-poly-top
  (equal (top-poly (top tag op bool poly))
         poly)
  :hints (("Goal" :in-theory (enable top top-bool top-op top-poly))))

(defthm top-bool-top
  (equal (top-bool (top tag op bool poly))
         bool)
  :hints (("Goal" :in-theory (enable top top-bool top-op top-poly))))

(defthm top-op-top
  (equal (top-op (top tag op bool poly))
         op)
  :hints (("Goal" :in-theory (enable top top-bool top-op top-poly))))

(defthm top-tag-top
  (equal (top-tag (top tag op bool poly))
         (if (and (poly-feature-p poly)
                  (bool-feature-p bool)) tag (tag nil)))
  :hints (("Goal" :in-theory (enable top top-tag top-bool top-op top-poly))))

(in-theory (disable weak-top-p op-p))

;; -------------------------------------------------------------------

(defun top-p (x)
  (declare (type t x))
  (and (weak-top-p x)
       (implies
        (feature-p (top-tag x))
        (and (poly-feature-p (top-poly x))
             (bool-feature-p (top-bool x))))
       (iff (evCex (top-poly x))
            (evCex (top-bool x)))))

(defthm top-p-implies-weak-top-p
  (implies
   (top-p x)
   (weak-top-p x))
  :rule-classes (:forward-chaining :type-prescription))

(defthm top-feature-property
  (implies
   (and
    (top-p x)
    (feature-p (top-tag x)))
   (and (poly-feature-p (top-poly x))
        (bool-feature-p (top-bool x))))
  :rule-classes (:rewrite :forward-chaining))

(defthm top-evcex-reduction
  (implies
   (top-p x)
   (iff (evCex (top-poly x))
        (evCex (top-bool x)))))

(defthm top-p-rewrite
  (iff (top-p (top tag op bool poly))
       (and
        (weak-top-p (top tag op bool poly))
        (implies
         (feature-p (if (and (poly-feature-p poly)
                             (bool-feature-p bool)) tag (tag nil)))
         (and (poly-feature-p poly)
              (bool-feature-p bool)))
        (iff (evCex poly)
             (evCex bool))))
  :hints (("Goal" :in-theory (disable poly-p))))

(defthm implies-top-p
  (implies
   (and
    (weak-top-p x)
    (iff (evCex (top-poly x))
         (evCex (top-bool x)))
    (implies
     (feature-p (top-tag x))
     (and (poly-feature-p (top-poly x))
          (bool-feature-p (top-bool x)))))
   (top-p x)))

(in-theory (disable top-p))

(def::un top-feature-p (x)
  (declare (xargs :signature ((top-p) booleanp)))
  (feature-p (top-tag x)))

(defthm top-feature-p-top
  (iff (top-feature-p (top tag op bool poly))
       (feature-p (if (and (poly-feature-p poly)
                           (bool-feature-p bool)) tag (tag nil)))))

(defthm feature-top-tag
  (iff (feature-p (top-tag x))
       (top-feature-p x)))

(in-theory (disable top-feature-p))

(theory-invariant
 (incompatible
  (:definition top-feature-p)
  (:rewrite feature-top-tag)))

(def::und and-expr (x y)
  (declare (xargs :signature ((boolean-expr-p boolean-expr-p) boolean-expr-p)))
  `(and ,x ,y))

(defthm evcex-and-expr
  (iff (evcex (and-expr x y))
       (and (evcex x)
            (evcex y)))
  :hints (("Goal" :in-theory (enable and-expr))))

(defthm evalt-and-expr
  (iff (evalt (and-expr x y) env)
       (and (evalt x env)
            (evalt y env)))
  :hints (("Goal" :in-theory (enable and-expr))))

(def::und or-expr (x y)
  (declare (xargs :signature ((boolean-expr-p boolean-expr-p) boolean-expr-p)))
  `(or ,x ,y))

(defthm evcex-or-expr
  (iff (evcex (or-expr x y))
       (or (evcex x)
           (evcex y)))
  :hints (("Goal" :in-theory (enable or-expr))))

(defthm evalt-or-expr
  (iff (evalt (or-expr x y) env)
       (or (evalt x env)
           (evalt y env)))
  :hints (("Goal" :in-theory (enable or-expr))))

(def::un top-gen (x)
  (declare (xargs :signature ((top-p) boolean-expr-p)))
  (if (and-op-p (top-op x))
      (and-expr (top-bool x) (top-poly x))
    (or-expr (top-bool x) (top-poly x))))

(defthm top-gen-top
  (implies
   (and (tag-p tag) (op-p op) (nf-p bool) (poly-p poly))
   (equal (top-gen (top tag op bool poly))
          (if (and-op-p op)
              (and-expr bool poly)
            (or-expr bool poly)))))

(defthm top-and-implication-false
  (implies
   (and
    (top-p x)
    (not (evcex (top-gen x))))
   (and (not (evcex (top-bool x)))
        (not (evcex (top-poly x)))))
  :rule-classes (:forward-chaining))

(defthm top-and-implication-true
  (implies
   (and
    (top-p x)
    (evcex (top-gen x)))
   (and (evcex (top-bool x))
        (evcex (top-poly x))))
  :rule-classes (:forward-chaining))

;; -------------------------------------------------------------------

(def::un and-tag (x y)
  (declare (xargs :signature ((tag-p tag-p) tag-p)))
  (tag (and (feature-p x) (feature-p y))))

;; -------------------------------------------------------------------

(def::und false-clause ()
  (declare (xargs :signature (() clause-p)))
  (clause (tag nil) nil))

(in-theory (disable (false-clause)))

(defthm ev-false-clause
  (and
   (iff (evcex (false-clause)) nil)
   (iff (evalt (false-clause) env) nil))
  :hints (("Goal" :in-theory (enable false-clause))))

(def::un select-one-false-clause (list)
  (declare (xargs :signature ((clause-listp) clause-p)
                  ))
  (if (endp list) (false-clause)
    (if (not (evCex (car list))) (car list)
      (select-one-false-clause (cdr list)))))

(defthm evcex-select-one-false-clause
  (implies
   (and
    (clause-listp x)
    (not (and-list (evcex-list x))))
   (and-list (not-list (evcex-list (clause-body (select-one-false-clause x))))))
  :hints (("Goal" :in-theory (enable evcex-clause-p))))

(defthm evalt-select-one-false-clause
  (implies
   (and (clause-listp list)
        (not (and-list (evcex-list list)))
        (and-list (evalt-list list env)))
   (not (and-list (not-list (evalt-list (clause-body (select-one-false-clause list)) env)))))
  :hints (("Goal" :induct (select-one-false-clause list)
           :in-theory (enable evalt-clause-p))))

;; -------------------------------------------------------------------

(def::und select-and-negate-one-clause (x)
  (declare (xargs :signature ((nf-p) cnf-p)
                  :guard (and (evcex x) (not-expr-p x))))
  ;; (not (and (or .. ) (or ..)))
  (let ((cnf (nf-cnf x)))
    (let ((clause (select-one-false-clause (cnf-body cnf))))
      (cnf (tag nil) (clausify-term-list (tag nil) (not-expr-list (clause-body clause)))))))

(defthm cnf-feature-p-choose-and-negate
  (not (cnf-feature-p (select-and-negate-one-clause x)))
  :hints (("Goal" :in-theory (e/d (select-and-negate-one-clause
                                   cnf-tag
                                   cnf-feature-p
                                   cnf)
                                  (feature-p-cnf-tag))))
  :rule-classes (:type-prescription
                 (:Forward-chaining :trigger-terms ((select-and-negate-one-clause x)))))

(defthm evcex-choose-and-negage-one
  (implies
   (and
    (nf-p x)
    (evcex x)
    (not-expr-p x))
   (evcex (select-and-negate-one-clause x)))
  :hints (("Goal" :in-theory (enable evcex-nf-p evcex-cnf-p select-and-negate-one-clause))))

(defthm evalt-rule-1
  (implies
   (and
    (nf-p x)
    (evcex x)
    (not-expr-p x)
    (not (evalt x env)))
   (not (evalt (select-and-negate-one-clause x) env)))
  :hints (("Goal" :in-theory (enable evalt-cnf-p evalt-nf-p evcex-cnf-p evcex-nf-p select-and-negate-one-clause))))

;; -------------------------------------------------------------------

(def::und and-clause-list (x y)
  (declare (xargs :signature ((clause-listp clause-listp) clause-listp)))
  (append x y))

(def::and and-clause-list
   :type-p clause-listp
   :both-p clause-feature-listp
   :true t
   :evcex (lambda (x) (and-list (evcex-list x)))
   :evalt (lambda (x env) (and-list (evalt-list x env)))
   )

;; -------------------------------------------------------------------

;; So this also should be complex ..

#+joe
(def::und and-clause-clause (x y)
  (declare (xargs :signature ((clause-p clause-p) clause-p clause-listp)))
  (let ((b1 (clause-body x))
        (b2 (clause-body y)))
    (if (and (consp b1) (consp b2) (equal (car b1) (car b2)))
        ;; (or x a b) (or x c d)
        ;; (or x a b c d)
        ;; 
      (mv x (list y)))))

(def::und and-cnf-TT (x y)
  (declare (xargs :signature ((cnf-p cnf-p) cnf-p)
                  :guard (and (evcex x) (evcex y))))
  (let ((res (and-clause-list (cnf-body x) (cnf-body y))))
    (let ((tag (and-tag (tag (clause-feature-listp res)) (and-tag (cnf-tag x) (cnf-tag y)))))
      (cnf tag res))))

(encapsulate
    ()

  (local (in-theory (enable evalt-cnf-p evcex-cnf-p)))

  (def::and and-cnf-TT
    :type-p cnf-p
    :both-p cnf-feature-p
    :true t
    )

  )

;; -------------------------------------------------------------------

(def::un singleton-p (x)
  (declare (xargs :signature ((nf-p) booleanp)))
  (let ((list (cnf-body (nf-cnf x))))
    (and (consp list) (null (cdr list)))))

(def::un get-singleton (x)
  (declare (xargs :signature (((lambda (x) (and (nf-p x) (singleton-p x)))) clause-p)))
  (car (cnf-body (nf-cnf x))))

(defthm evcex-singleton-p
  (implies
   (and
    (singleton-p x)
    (nf-p x))
   (iff (evcex x)
        (if (not-expr-p x)
            (not (or-list (evcex-list (clause-body (get-singleton x)))))
          (or-list (evcex-list (clause-body (get-singleton x)))))))
  :hints (("Goal" :in-theory (enable evcex-clause-p evcex-clause evcex-nf-p evcex-cnf-p))))

(defthm evalt-singleton-p
  (implies
   (and
    (singleton-p x)
    (nf-p x))
   (iff (evalt x env)
        (if (not-expr-p x)
            (not (or-list (evalt-list (clause-body (get-singleton x)) env)))
          (or-list (evalt-list (clause-body (get-singleton x)) env)))))
  :hints (("Goal" :in-theory (enable evalt-clause-p evalt-clause evalt-nf-p evalt-cnf-p))))

(def::un singleton! (tag x)
  (declare (xargs :signature ((tag-p clause-p) (lambda (x) (and (nf-p x) (singleton-p x))))))
  (nf (cnf (if (clause-feature-p x) tag (tag nil)) (list x))))

(defthm not-not-expr-p-singleton!
  (not (not-expr-p (singleton! tag x)))
  :hints (("Goal" :in-theory (enable nf)))
  :rule-classes ((:forward-chaining :trigger-terms ((singleton! tag x)))))

(defthm feature-p-singleton!
  (implies
   (and (clause-p x) (tag-p tag))
   (iff (bool-feature-p (singleton! tag x))
        (feature-p (if (clause-feature-p x) tag (tag nil))))))

(defthm get-singleton-singleton!
  (implies
   (and (clause-p x) (tag-p tag))
   (equal (get-singleton (singleton! tag x))
          x)))

(defthm get-singleton-not-expr
  (implies
   (nf-p x)
   (equal (get-singleton (not-expr x))
          (get-singleton x))))

(defthm singleton-not-expr
  (implies
   (nf-p x)
   (iff (singleton-p (not-expr x))
        (singleton-p x))))

(in-theory (disable singleton-p singleton! get-singleton))

;; -------------------------------------------------------------------

(def::un atom-p (x)
  (declare (xargs :signature ((nf-p) booleanp)))
  (and (not (not-expr-p x))
       (singleton-p x)
       (let ((clause (get-singleton x)))
         (and (consp (clause-body clause))
              (null (cdr (clause-body clause)))))))

(defthm atom-p-implies-singleton-p
  (implies
   (atom-p x)
   (singleton-p x))
  :rule-classes (:forward-chaining))

(def::un get-atom (x)
  (declare (xargs :signature (((lambda (x) (and (nf-p x) (atom-p x)))) boolean-term-p)))
  (car (clause-body (get-singleton x))))

(defthm evcex-atom-p
  (implies
   (and
    (atom-p x)
    (nf-p x))
   (iff (evcex x)
        (evcex (get-atom x))))
  :hints (("Goal" :in-theory (enable evcex-clause evcex-nf-p evcex-cnf-p))))

(defthm evalt-atom-p
  (implies
   (and
    (atom-p x)
    (nf-p x))
   (iff (evalt x env)
        (evalt (get-atom x) env)))
  :hints (("Goal" :in-theory (enable evalt-clause evalt-nf-p evalt-cnf-p))))

(def::un atom! (tag x)
  (declare (xargs :signature ((tag-p boolean-term-p) (lambda (x) (and (nf-p x) (atom-p x))))))
  (singleton! tag (clause tag (list x))))

(defthm feature-p-atom!
  (implies
   (and (boolean-term-p x) (tag-p tag))
   (iff (bool-feature-p (atom! tag x))
        (feature-p tag))))

(defthm get-atom-atom!
  (implies
   (and (boolean-term-p x) (tag-p tag))
   (equal (get-atom (atom! tag x))
          x)))

(defthm not-not-expr-p-atom-p
  (implies
   (atom-p x)
   (not (not-expr-p x)))
  :rule-classes :forward-chaining)

(in-theory (disable atom-p atom! get-atom))

;; -------------------------------------------------------------------

(def::un or-with-all (clause list)
  (declare (xargs :signature ((clause-p clause-listp) clause-listp)))
  (if (endp list) nil
    (let ((c1 (car list)))
      (cons (clause (and-tag (clause-tag clause)
                             (clause-tag c1))
                    (append (clause-body clause)
                            (clause-body c1)))
            (or-with-all clause (cdr list))))))

(defthm evcex-or-with-all
  (implies
   (and
    (clause-p clause)
    (clause-listp list))
   (iff (and-list (evcex-list (or-with-all clause list)))
        (or (evcex clause)
            (and-list (evcex-list list)))))
  :hints (("Goal" :in-theory (enable evcex-clause-p))))
         
(defthm evalt-or-with-all
  (implies
   (and
    (clause-p clause)
    (clause-listp list))
   (iff (and-list (evalt-list (or-with-all clause list) env))
        (or (evalt clause env)
            (and-list (evalt-list list env)))))
  :hints (("Goal" :in-theory (enable evalt-clause-p))))

(defthm clause-feature-listp-or-with-all
  (iff (clause-feature-listp (or-with-all clause list))
       (or (not (consp list))
           (and (clause-feature-p clause)
                (clause-feature-listp list)))))

(in-theory (disable or-with-all))

;; -------------------------------------------------------------------
;;
;; AXIOM 1:
;; (thm (iff (and   (not (and (or x y z)))   (not (and (or a b c) (or d e f))))
;;           (not (and (or a b c x y z) (or d e f x y z)))))
;;
;; AXIOM 2:
;; (thm (iff (and   (not (and (or x y z)))   (and (or a b c) (or d e f)))
;;           (and (not x) (not y) (not z) (or a b c) (or d e f))))
;;
;; -------------------------------------------------------------------

(def::un defeature-bool (x)
  (declare (xargs :signature ((nf-p) nf-p)))
  (let ((nf (nf (cnf (tag nil) (cnf-body (nf-cnf x))))))
    (if (not-expr-p x) (not-expr nf) nf)))

(def::un and-choose-bool (x y)
  (declare (xargs :signature ((nf-p nf-p) nf-p)))
  (defeature-bool (if (and (not (evcex x)) (not (evcex y))) (if (lexorder x y) x y)
                    (if (not (evcex x)) x y))))

(def::und and-singleton (x y)
  (declare (xargs :signature (((lambda (x) (and (nf-p x) (not-expr-p x) (singleton-p x))) nf-p) nf-p)))
  (let ((clause (get-singleton x))
        (tag (and-tag (nf-tag x) (nf-tag y))))
    (if (not-expr-p y)
        (not-expr (nf (cnf tag (or-with-all clause (cnf-body (nf-cnf y))))))
      (if (not (and (evcex x) (evcex y))) (and-choose-bool x y)
        (nf (cnf tag (append (clausify-term-list tag (not-expr-list (clause-body clause)))
                             (cnf-body (nf-cnf y)))))))))

(def::and and-singleton
  :xtype-p (lambda (x) (and (nf-p x) (not-expr-p x) (singleton-p x)))
  :ytype-p nf-p
  :both-p bool-feature-p
  :true t
  :false t
  :hints ((and stable-under-simplificationp
               '(:in-theory (enable evcex-clause-p evalt-clause-p evalt-nf-p evalt-cnf-p evcex-nf-p evcex-cnf-p)))
          (and stable-under-simplificationp
               '(:in-theory (enable evcex-clause-p evalt-clause-p singleton-p get-singleton))))
  )

(defthm clause-feature-from-singleton-bool-feature
  (implies
   (and
    (nf-p y)
    (singleton-p y)
    (bool-feature-p y))
   (clause-feature-p (get-singleton y)))
  :hints (("Goal" :in-theory (e/d (bool-feature-p 
                                   cnf-feature-p
                                   clause-feature-p
                                   nf-cnf
                                   clause-tag
                                   cnf-body
                                   cnf-tag
                                   clause-p
                                   cnf-p nf-p singleton-p get-singleton)
                                  (FEATURE-CLAUSE-TAG
                                   CNF-FEATURE-NF-CNF
                                   FEATURE-P-CNF-TAG)))))

(defthm clause-feature-listp-from-singleton-bool-feature
  (implies
   (and
    (nf-p y)
    (bool-feature-p y))
   (CLAUSE-FEATURE-LISTP (CNF-BODY (NF-CNF Y))))
  :hints (("Goal" :in-theory (e/d (bool-feature-p 
                                   cnf-feature-p
                                   clause-feature-p
                                   nf-cnf
                                   clause-tag
                                   cnf-body
                                   cnf-tag
                                   clause-p
                                   cnf-p nf-p singleton-p get-singleton)
                                  (FEATURE-CLAUSE-TAG
                                   CNF-FEATURE-NF-CNF
                                   FEATURE-P-CNF-TAG)))))

(defthm bool-feature-p-and-singleton
  (implies
   (and
    (nf-p x)
    (not-expr-p x)
    (singleton-p x)
    (nf-p y)
    (not-expr-p y)
    )
   (iff (bool-feature-p (and-singleton x y))
        (and (bool-feature-p x)
             (bool-feature-p y))))
  :hints (("Goal" :in-theory (enable and-singleton))))

;; -------------------------------------------------------------------
;; AXIOM 3:
;; (thm (iff (and   (and (or x))             (and (or a))) 
;;           (not (and (or (not x) (not a))))))
;;
;; -------------------------------------------------------------------

(def::und and-atom (x y)
  (declare (xargs :signature (((lambda (x) (and (nf-p x) (atom-p x))) 
                               (lambda (x) (and (nf-p x) (atom-p x))))
                              nf-p)))
  (let ((tag (tag (and (bool-feature-p x) (bool-feature-p y)))))
    (not-expr (singleton! tag (clause tag (list (not-expr (get-atom x))
                                                (not-expr (get-atom y))))))))

(def::and and-atom
  :xtype-p (lambda (x) (and (nf-p x) (atom-p x)))
  :ytype-p (lambda (x) (and (nf-p x) (atom-p x)))
  :both-p bool-feature-p
  :true t
  :false t
  )

(defthm feature-p-and-atom
  (implies
   (and
    (nf-p x)
    (atom-p x)
    (nf-p y)
    (atom-p y))
   (iff (bool-feature-p (and-atom x y))
        (and (bool-feature-p x)
             (bool-feature-p y))))
  :hints (("Goal" :in-theory (enable and-atom))))

;; -------------------------------------------------------------------

;; -------------------------------------------------------------------

(def::un atom-to-singleton (x)
  (declare (xargs :signature (((lambda (x) (and (nf-p x) (atom-p x)))) (lambda (x) (and (nf-p x) (singleton-p x) (not-expr-p x))))))
  (not-expr (singleton! (nf-tag x) (clause (nf-tag x) (list (not-expr (get-atom x)))))))

(defthm evcex-atom-to-singleton
  (implies
   (and
    (nf-p x)
    (atom-p x))
   (iff (evcex (atom-to-singleton x))
        (evcex x)))
  :hints (("Goal" :in-theory (enable atom-p singleton! evcex-nf evcex-cnf get-atom))))

(defthm evalt-atom-to-singleton
  (implies
   (and
    (nf-p x)
    (atom-p x))
   (iff (evalt (atom-to-singleton x) env)
        (evalt x env)))
  :hints (("Goal" :in-theory (enable atom-p singleton! evalt-nf evalt-cnf get-atom))))

(defthm feature-p-atom-to-singleton
  (implies
   (and
    (nf-p x)
    (atom-p x))
   (iff (bool-feature-p (atom-to-singleton x))
        (bool-feature-p x))))

(in-theory (disable atom-to-singleton))

;; -------------------------------------------------------------------

(def::und and-bool (x y)
  (declare (xargs :signature ((nf-p nf-p) nf-p)
                  :guard-hints (("Goal" :in-theory (enable evcex-nf-p)))))
  (if (and (atom-p x) (atom-p y))
      (and-atom x y)
    (if (or (atom-p x) (and (singleton-p x) (not-expr-p x)))
        (let ((x (if (not (atom-p x)) x (atom-to-singleton x))))
          (and-singleton x y))
      (if (or (atom-p y) (and (singleton-p y) (not-expr-p y)))
          (let ((y (if (not (atom-p y)) y (atom-to-singleton y))))
            (and-singleton y x))
        (if (not (and (evcex x) (evcex y))) 
            (and-choose-bool x y)
          (let ((x (if (not-expr-p x) (select-and-negate-one-clause x) (nf-cnf x)))
                (y (if (not-expr-p y) (select-and-negate-one-clause y) (nf-cnf y))))
            (nf (and-cnf-TT x y))))))))

(def::and and-bool
  :type-p nf-p
  :both-p bool-feature-p
  :true t
  :false t
  :hints (("Goal" :in-theory (disable evcex-atom-p evcex-singleton-p evalt-atom-p evalt-singleton-p))
          (and stable-under-simplificationp
               '(:in-theory (e/d (evcex-nf-p evcex-cnf-p evalt-nf-p evalt-cnf-p) 
                                 (evcex-atom-p evcex-singleton-p evalt-atom-p evalt-singleton-p)))))
  )

(defthm feature-p-and-bool-1
  (implies
   (and
    (nf-p x)
    (nf-p y)
    (atom-p x) 
    (atom-p y))
   (iff (bool-feature-p (and-bool x y))
        (and (bool-feature-p x)
             (bool-feature-p y))))
  :hints (("Goal" :in-theory (enable and-bool))))

(defthm feature-p-and-bool-2
  (implies
   (and
    (nf-p x)
    (nf-p y)
    (or (singleton-p x) (singleton-p y))
    (not-expr-p x)
    (not-expr-p y))
   (iff (bool-feature-p (and-bool x y))
        (and (bool-feature-p x)
             (bool-feature-p y))))
  :hints (("Goal" :in-theory (enable and-bool))))

;; -------------------------------------------------------------------

(def::un not-poly (x)
  (declare (xargs :signature ((poly-p) poly-p)))
  (poly (poly-tag x) (not-expr (poly-expr x))))

(defthm poly-expr-not-poly
  (equal (poly-expr (not-poly x))
         (not-expr (poly-expr x))))

(defthm feature-p-not-poly
  (implies
   (poly-p x)
   (equal (poly-feature-p (not-poly x))
          (poly-feature-p x))))

(defthm evcex-not-poly
  (implies
   (poly-p x)
   (iff (evcex (not-poly x))
        (not (evcex x))))
  :hints (("Goal" :in-theory (enable evcex-poly-p))))

(defthm evalt-not-poly
  (implies
   (poly-p x)
   (iff (evalt (not-poly x) env)
        (not (evalt x env))))
  :hints (("Goal" :in-theory (enable evalt-poly-p))))

(in-theory (disable not-poly))

;; -------------------------------------------------------------------

(def::und and-poly (x y)
  (declare (xargs :signature ((poly-p poly-p) poly-p)))
  (poly (and-tag (poly-tag x) (poly-tag y))
        (and-expr (poly-expr x) (poly-expr y))))

(def::and and-poly
  :type-p poly-p
  :both-p poly-feature-p
  :true t
  :false t
  :hints ((and stable-under-simplificationp
               '(:in-theory (enable evcex-poly-p evalt-poly-p))))
  )

;; -------------------------------------------------------------------

(def::un boolean-only-p (x)
  (declare (xargs :signature ((top-p) booleanp)))
  (let ((expr (poly-expr (top-poly x))))
    (case-match expr
      (('lit v) (and (poly-feature-p (top-poly x))
                     (if (and-op-p (top-op x)) (not (not v)) (not v))))
      (& nil))))

(defthm boolean-only-implies-poly-feature
  (implies
   (boolean-only-p x)
   (poly-feature-p (top-poly x)))
  :rule-classes (:forward-chaining))

(defthm evcex-boolean-only-p
  (implies
   (and
    (top-p x)
    (boolean-only-p x))
   (iff (evcex (top-gen x))
        (evcex (top-bool x))))
  :hints (("Goal" :in-theory (enable evcex-poly-p))))

(defthm evalt-boolean-only-p
  (implies
   (and
    (top-p x)
    (boolean-only-p x))
   (iff (evalt (top-gen x) env)
        (evalt (top-bool x) env)))
  :hints (("Goal" :in-theory (enable evalt-poly-p))))

(in-theory (disable boolean-only-p))

;; -------------------------------------------------------------------

(def::un poly-only-p (x)
  (declare (xargs :signature ((top-p) booleanp)))
  (let ((nf (top-bool x)))
    (and (bool-feature-p (top-bool x))
         (null (cnf-body (nf-cnf nf)))
         (if (and-op-p (top-op x))
             (not (not-expr-p nf))
           (not-expr-p nf)))))

(defthm poly-only-implies-bool-feature
  (implies
   (poly-only-p x)
   (bool-feature-p (top-bool x)))
  :rule-classes (:forward-chaining))

(defthm evcex-poly-only-p
  (implies
   (and
    (top-p x)
    (poly-only-p x))
   (iff (evcex (top-gen x))
        (evcex (top-poly x))))
  :hints (("Goal" :in-theory (enable evcex-nf-p evcex-cnf-p))))

(defthm evalt-poly-only-p
  (implies
   (and
    (top-p x)
    (poly-only-p x))
   (iff (evalt (top-gen x) env)
        (evalt (top-poly x) env)))
  :hints (("Goal" :in-theory (enable evalt-nf-p evalt-cnf-p))))

(in-theory (disable poly-only-p))

;; -------------------------------------------------------------------

(def::un true-poly ()
  (declare (xargs :signature (() poly-p)))
  (poly (tag t) `(lit t)))

(in-theory (disable (true-poly)))

(def::un false-poly ()
  (declare (xargs :signature (() poly-p)))
  (poly (tag t) `(lit nil)))

(in-theory (disable (false-poly)))

(def::un top-bool-only (t0 b)
  (declare (xargs :signature ((tag-p nf-p) top-p)))
  (let* ((cex (evcex b))
         (tag (and-tag t0 (tag (bool-feature-p b)))))
    (if cex (top tag :and b (true-poly))
      (top tag :or b (false-poly)))))

(defthm evcex-top-bool-only
  (implies
   (and (tag-p tag) (nf-p x))
   (iff (evcex (top-gen (top-bool-only tag x)))
        (evcex x))))

(defthm evalt-top-bool-only
  (implies
   (and (nf-p x) (tag-p tag))
   (iff (evalt (top-gen (top-bool-only tag x)) env)
        (evalt x env))))

(defthm top-feature-top-bool
  (implies
   (and (nf-p x) (tag-p tag))
   (iff (top-feature-p (top-bool-only tag x))
        (and (feature-p tag) (bool-feature-p x)))))

(in-theory (disable top-bool-only (top-bool-only)))

;; -------------------------------------------------------------------

(def::un true-bool ()
  (declare (xargs :signature (() nf-p)))
  (nf (cnf (tag t) nil)))

(in-theory (disable (true-bool)))

(def::un false-bool ()
  (declare (xargs :signature (() nf-p)))
  (not-expr (true-bool)))

(in-theory (disable (false-bool)))

(def::un top-poly-only (t0 b)
  (declare (xargs :signature ((tag-p poly-p) top-p)))
  (let* ((cex (evcex b))
         (tag (and-tag t0 (tag (poly-feature-p b)))))
    (if cex (top tag :and (true-bool) b)
      (top tag :or (false-bool) b))))

(defthm evcex-top-poly-only
  (implies
   (and (tag-p tag) (poly-p x))
   (iff (evcex (top-gen (top-poly-only tag x)))
        (evcex x))))

(defthm evalt-top-poly-only
  (implies
   (and (tag-p tag) (poly-p x))
   (iff (evalt (top-gen (top-poly-only tag x)) env)
        (evalt x env))))

(defthm top-feature-top-poly-only
  (implies
   (and (tag-p tag) (poly-p x))
   (equal (top-feature-p (top-poly-only tag x))
          (and (feature-p tag) (poly-feature-p x)))))

(in-theory (disable top-poly-only (top-poly-only)))

;; -------------------------------------------------------------------

(def::un true-top ()
  (declare (xargs :signature (() top-p)))
  (top (tag t) :and (true-bool) (true-poly)))

(def::un always-true-p (x)
  (declare (xargs :signature ((top-p) booleanp)))
  (and (top-feature-p x)
       (equal (top-op x) :and)
       (equal (top-bool x) (true-bool))
       (equal (top-poly x) (true-poly))))

(defthm always-true-true-top
  (always-true-p (true-top)))

(defthm evcex-always-true-p
  (implies
   (always-true-p x)
   (iff (evcex (top-gen x)) t)))

(defthm evalt-true-top-p
  (implies
   (always-true-p x)
   (iff (evalt (top-gen x) env) t)))

(defthm top-feature-true-top
  (implies
   (always-true-p x)
   (top-feature-p x)))

(def::un false-top ()
  (declare (xargs :signature (() top-p)))
  (top (tag t) :or (not-expr (true-bool)) (not-poly (true-poly))))

(def::un always-false-p (x)
  (declare (xargs :signature ((top-p) booleanp)))
  (and (top-feature-p x)
       (equal (top-bool x) (not-expr (true-bool)))
       (equal (top-poly x) (not-poly (true-poly)))))

(defthm always-false-false-top
  (always-false-p (false-top)))

(defthm evcex-always-false-p
  (implies
   (always-false-p x)
   (iff (evcex (top-gen x)) nil)))

(defthm evalt-false-top-p
  (implies
   (always-false-p x)
   (iff (evalt (top-gen x) env) nil)))

(defthm top-feature-false-top
  (implies
   (always-false-p x)
   (top-feature-p x)))

(defthm always-inconsistency
  (implies
   (always-true-p x)
   (not (always-false-p x)))
  :hints (("Goal" :in-theory (enable nf cnf not-expr))))

(in-theory (disable always-true-p true-top (true-top)))
(in-theory (disable always-false-p false-top (false-top)))

;; -------------------------------------------------------------------

(encapsulate
    (
     (top-choice (x y) t :guard (and (top-p x) (top-p y)))
     )
  
  (local
   (defun top-choice (x y)
     (declare (xargs :guard (and (top-p x) (top-p y)))
              (ignore x y))
     :x))
  
  )

(def::un defeature-top (x)
  (declare (xargs :signature ((top-p) top-p)))
  (top (tag nil) (top-op x)
       (top-bool x) (top-poly x)))

(defthm top-gen-defeature-top
  (implies
   (top-p x)
   (equal (top-gen (defeature-top x))
          (top-gen x))))

(defthm feature-p-defeature-top
  (not (top-feature-p (defeature-top x))))

;;(in-theory (disable defeature-top))

(def::un and-choose-top (x y)
  (declare (xargs :signature ((top-p top-p) top-p)))
  (defeature-top (if (not (evcex (top-gen x))) x y)))

;; -------------------------------------------------------------------

(def::un one-only-p (x)
  (declare (xargs :signature ((top-p) booleanp)))
  (or (poly-only-p x) (boolean-only-p x)))

(defun and-and-guard-p (x)
  (declare (type t x))
  (and (top-p x) (or (one-only-p x) (and-op-p (top-op x)))))

(def::und and-top-and-and (x y)
  (declare (xargs :signature ((top-p top-p) top-p)
                  :guard (and (and-op-p (top-op x))
                              (and-op-p (top-op y)))))
  (top (tag (and (top-feature-p x) (top-feature-p y)))
       :and 
       (and-bool (top-bool x) (top-bool y))
       (and-poly (top-poly x) (top-poly y))))


(def::and and-top-and-and
  :type-p (lambda (x) (and (top-p x) (and-op-p (top-op x))))
  :gen top-gen
  :both-p top-feature-p
  :true t
  :false t
  )

(in-theory (disable one-only-p and-and-guard-p))

;; -------------------------------------------------------------------

(def::und and-top-or-or (x y)
  (declare (xargs :signature ((top-p (lambda (y) (and (top-p y) (iff (evcex (top-gen x)) (evcex (top-gen y)))))) top-p)
                  :guard (and (not (and-op-p (top-op x)))
                              (not (and-op-p (top-op y))))))
  (and-choose-top (top (tag nil) :and (top-bool x) (top-poly y))
              (top (tag nil) :and (top-bool y) (top-poly x))))

(def::and and-top-or-or
  :type-p (lambda (x) (and (top-p x) (not (and-op-p (top-op x)))))
  :gen top-gen
  :both-p top-feature-p
  :true t
  :weak t
  )

;; -------------------------------------------------------------------

(def::und and-top-and-or (x y)
  (declare (xargs :signature ((top-p (lambda (y) (and (top-p y) (iff (evcex (top-gen x)) (evcex (top-gen y)))))) top-p)
                  :guard (and (and-op-p (top-op x))
                              (not (and-op-p (top-op y))))))
  (and-choose-top (top (tag nil) :and (top-bool x) (and-poly (top-poly x) (top-poly y)))
              (top (tag nil) :and (and-bool (top-bool x) (top-bool y)) (top-poly x))))

(def::and and-top-and-or
  :xtype-p (lambda (x) (and (top-p x) (and-op-p (top-op x))))
  :ytype-p (lambda (y) (and (top-p y) (not (and-op-p (top-op y)))))
  :gen top-gen
  :both-p top-feature-p
  :true t
  :weak t
  )

;; -------------------------------------------------------------------

;; Transition to cex equal cases here .. resolve false cases where
;; needed.
(def::und and-top (x y)
  (declare (xargs :signature ((top-p top-p) top-p)))
  (if (always-true-p y) x
    (if (always-true-p x) y
      (if (and (always-false-p x) (top-feature-p y)) x
        (if (and (always-false-p y) (top-feature-p x)) y
          (if (and (boolean-only-p x)
                   (boolean-only-p y))
              (top-bool-only (tag (and (top-feature-p x) (top-feature-p y))) (and-bool (top-bool x) (top-bool y)))
            (if (and (poly-only-p x)
                     (poly-only-p y))
                (top-poly-only (tag (and (top-feature-p x) (top-feature-p y))) (and-poly (top-poly x) (top-poly y)))
              (if (not (iff (evcex (top-gen x)) (evcex (top-gen y))))
                  (and-choose-top x y)
                (if (not (iff (evcex (top-gen x)) (evcex (top-gen y))))
                    (and-choose-top x y)
                  (if (and-op-p (top-op x))
                      (if (and-op-p (top-op y))
                          (and-top-and-and x y)
                        (if (evcex (top-gen x)) 
                            (and-top-and-or x y)
                          (and-choose-top x y)))
                    (if (and-op-p (top-op y))
                        (if (evcex (top-gen x)) 
                            (and-top-and-or y x)
                          (and-choose-top x y))
                      (if (evcex (top-gen x))
                          (and-top-or-or x y)
                        (and-choose-top x y)))))))))))))

(in-theory (disable top-gen))

(def::and and-top
  :type-p top-p
  :true t
  :false t
  :gen top-gen
  :both-p top-feature-p
  :hints ((and stable-under-simplificationp
               '(:in-theory (enable always-true-p always-false-p top-gen))))
  )

(defthm evalt-and-top-always-true-1
  (implies
   (always-true-p y)
   (equal (and-top x y)
          x))
  :hints (("Goal" :in-theory (enable and-top))))

(encapsulate
    ()

  (local
   (defthm open-equal-on-consp
     (implies
      (and (consp x) (consp y))
      (iff (equal x y)
           (and (equal (car x) (car y))
                (equal (cdr x) (cdr y)))))))

  (defthm evalt-and-top-always-true-2
    (implies
     (and (top-p x) (top-p y) (always-true-p x))
     (equal (and-top x y)
            y))
    :hints (("Goal" :in-theory (e/d (feature-p weak-top-p top-op top-tag top-feature-p top-p top-bool top-poly always-true-p and-top)
                                    (FEATURE-TOP-TAG)))))

  )

;; -------------------------------------------------------------------
;;
;; AXIOM 5:
;;  Atoms are never negated.
;;
;; -------------------------------------------------------------------
(def::un not-bool (x)
  (declare (xargs :signature ((nf-p) nf-p)))
  (if (atom-p x) (atom! (tag (bool-feature-p x)) (not-expr (get-atom x)))
    (if (not-expr-p x) (nf (nf-cnf x))
      (not-expr x))))

(defthm evcex-not-bool
  (implies
   (nf-p x)
   (iff (evcex (not-bool x))
        (not (evcex x))))
  :hints ((and stable-under-simplificationp
               '(:in-theory (enable evcex-nf-p evcex-cnf-p)))))

(defthm evalt-not-bool
  (implies
   (nf-p x)
   (iff (evalt (not-bool x) env)
        (not (evalt x env))))
  :hints ((and stable-under-simplificationp
               '(:in-theory (enable evalt-nf-p evalt-cnf-p)))))

(defthm bool-feature-not-bool
  (implies
   (nf-p x)
   (iff (bool-feature-p (not-bool x))
        (bool-feature-p x))))

(in-theory (disable not-bool))

;; -------------------------------------------------------------------

(def::un not-top (x)
  (declare (xargs :signature ((top-p) top-p)))
  (let ((bool (top-bool x))
        (poly (top-poly x)))
    (top (top-tag x) (not-op (top-op x))
         (not-bool bool) (not-poly poly))))

(defthm evcex-not-top
  (implies
   (top-p x)
   (iff (evcex (top-gen (not-top x)))
        (not (evcex (top-gen x))))))

(defthm evalt-not-top
  (implies
   (top-p x)
   (iff (evalt (top-gen (not-top x)) env)
        (not (evalt (top-gen x) env))))
  :hints ((and stable-under-simplificationp
               '(:in-theory (enable top-gen)))))

(defthm top-feature-not-top
  (implies
   (top-p x)
   (iff (top-feature-p (not-top x))
        (top-feature-p x))))

;; -------------------------------------------------------------------

(defun top-listp (x)
  (declare (type t x))
  (if (not (consp x)) (null x)
    (and (top-p (car x))
         (top-listp (cdr x)))))

(defun top-feature-listp (x)
  (declare (type (satisfies top-listp) x))
  (if (not (consp x)) t
    (and (top-feature-p (car x))
         (top-feature-listp (cdr x)))))

(def::un top-gen-list (x)
  (declare (xargs :signature ((top-listp) boolean-expr-listp)))
  (if (not (consp x)) nil
    (cons (top-gen (car x))
          (top-gen-list (cdr x)))))

(def::un not-top-list (list)
  (declare (xargs :signature ((top-listp) top-listp)))
  (if (not (consp list)) nil
    (cons (not-top (car list))
          (not-top-list (cdr list)))))

(defthm promote-not-top-list
  (implies
   (top-listp list)
   (bool-equiv-list (evcex-list (top-gen-list (not-top-list list)))
                    (not-list (evcex-list (top-gen-list list))))))

;; -------------------------------------------------------------------

(def::un keep-false-top-list (list)
  (declare (xargs :signature ((top-listp) top-listp)))
  (if (not (consp list)) nil
    (let ((top (car list)))
      (if (evcex (top-gen top)) (keep-false-top-list (cdr list))
        (cons top (keep-false-top-list (cdr list)))))))

(def::un all-false-top-listp (list)
  (declare (xargs :signature ((top-listp) booleanp)))
  (if (not (consp list)) t
    (and (not (evcex (top-gen (car list))))
         (all-false-top-listp (cdr list)))))

(defthm all-false-top-listp-keep-false-top-list
  (implies
   (top-listp list)
   (all-false-top-listp (keep-false-top-list list))))

(defthm evcex-all-false-top-listp
  (implies
   (and
    (top-listp list)
    (all-false-top-listp list))
   (iff (and-list (evcex-list (top-gen-list list)))
        (not (consp list)))))

(defthm evalt-keep-false-top-list
  (implies
   (and
    (top-listp list)
    (and-list (evalt-list (top-gen-list list) env)))
   (and-list (evalt-list (top-gen-list (keep-false-top-list list)) env))))

(defthm non-empty-keep-false-top-list
  (implies
   (and
    (top-listp list)
    (not (and-list (evcex-list (top-gen-list list)))))
   (consp (keep-false-top-list list))))

(defthm not-and-list-implies-consp-list
  (implies
   (not (and-list list))
   (consp list)))

(defthm consp-top-gen-list
  (iff (consp (top-gen-list list))
       (consp list)))

(defthm consp-evcex-list
  (iff (consp (evcex-list list))
       (consp list))
  :hints (("Goal" :induct (len list))))

;; -------------------------------------------------------------------

(def::un and-top-list-rec (list)
  (declare (xargs :signature ((top-listp) top-p)))
  (if (not (consp list)) (true-top)
    (let ((top (car list)))
      (and-top top (and-top-list-rec (cdr list)))))) 

(defthm evcex-and-top-list-rec
  (implies
   (top-listp list)
   (iff (evcex (top-gen (and-top-list-rec list)))
        (and-list (evcex-list (top-gen-list list))))))

(defthm evalt-and-top-list-rec
  (implies
   (and
    (top-listp list)
    (top-feature-p (and-top-list-rec list)))
   (iff (evalt (top-gen (and-top-list-rec list)) env)
        (and-list (evalt-list (top-gen-list list) env)))))

(defthm inv2-T-and-top-list-rec
  (implies 
   (and 
    (top-listp list)
    (and-list (evcex-list (top-gen-list list)))
    (not (and-list (evalt-list (top-gen-list list) env))))
   (not (evalt (top-gen (and-top-list-rec list)) env))))

(defthm inv2-F-and-top-list-rec
  (implies 
   (and (top-listp list)
        (all-false-top-listp list)
        (and-list (evalt-list (top-gen-list list) env)))
   (evalt (top-gen (and-top-list-rec list)) env))
  :hints (("Goal" :induct (and-top-list-rec list)
           :do-not-induct t)
          (and stable-under-simplificationp
               '(:cases ((consp (cdr list)))
                        :do-not-induct t))))

(defthm top-feature-p-and-top-list-rec
  (implies
   (and
    (top-listp list)
    (top-feature-p (and-top-list-rec list)))
   (top-feature-listp list)))

;; -------------------------------------------------------------------

(in-theory (disable defeature-top))

(def::un and-top-list (list)
  (declare (xargs :signature ((top-listp) top-p)))
  (let ((top (and-top-list-rec list)))
    (if (evcex (top-gen top)) top
      (if (top-feature-p top) top
        (defeature-top (and-top-list-rec (keep-false-top-list list)))))))

(defthm evcex-and-top-list
  (implies
   (top-listp list)
   (iff (evcex (top-gen (and-top-list list)))
        (and-list (evcex-list (top-gen-list list)))))
  :hints (("Goal" :do-not-induct t)))

(defthm evalt-and-top-list
  (implies
   (and
    (top-listp list)
    (top-feature-p (and-top-list list)))
   (iff (evalt (top-gen (and-top-list list)) env)
        (and-list (evalt-list (top-gen-list list) env))))
  :hints (("Goal" :do-not-induct t)))

(defthm inv2-T-and-top-list
  (implies
   (and
    (top-listp list)
    (and-list (evcex-list (top-gen-list list)))
    (not (and-list (evalt-list (top-gen-list list) env))))
   (not (evalt (top-gen (and-top-list list)) env)))
  :hints (("Goal" :do-not-induct t)))

(defthm inv2-F-and-top-list
  (implies
   (and
    (top-listp list)
    (not (and-list (evcex-list (top-gen-list list))))
    (and-list (evalt-list (top-gen-list list) env)))
   (evalt (top-gen (and-top-list list)) env))
  :hints (("Goal" :do-not-induct t)))

(defthm top-feature-p-and-top-list
  (implies
   (and
    (top-listp list)
    (top-feature-p (and-top-list list)))
   (top-feature-listp list)))

(in-theory (disable and-top-list))

;; -------------------------------------------------------------------

;; (defthm inv1-and-top-list
;;   (implies
;;    (top-listp list)
;;    (iff (evcex (top-gen (and-top-list list)))
;;         (and-list (evcex-list (top-gen-list list))))))

;; (defthm inv2-and-top-list
;;   (implies
;;    (and
;;     (top-feature-p (and-top-list list))
;;     (top-listp list))
;;    (iff (evalt (top-gen (and-top-list list)) env)
;;         (and-list (evalt-list (top-gen-list list) env)))))

;; (defthm
;;   (implies
;;    (and
;;     (top-listp list)
;;     (not (or-list (evcex-list (top-gen-list list))))
;;     )
;;    (
;; (defthm top-feature-p-and-top-list
;;   (implies
;;    (and
;;     (top-feature-p (and-top-list list))
;;     (top-listp list))
;;    (top-feature-listp list)))

;; ;; -------------------------------------------------------------------

;; (def::un or-top-list (list)
;;   (declare (xargs :signature ((top-listp) top-p)))
;;   (not-top (and-top-list (not-top-list list))))

