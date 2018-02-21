;; 
;; Copyright (C) 2017, Rockwell Collins
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;; 
;; 
(in-package "ACL2")
(include-book "coi/util/defun" :dir :system)

(defun nfix-equiv (x y)
  (declare (type t x y))
  (equal (nfix x) (nfix y)))

(defthm nfix-natp
  (implies
   (natp x)
   (equal (nfix x) x)))

(defequiv nfix-equiv)

(defcong nfix-equiv equal (nfix x) 1)

(defthm nfix-equiv-nfix
  (nfix-equiv (nfix x) x))

(defcong nfix-equiv equal (zp x) 1)

(in-theory (disable nfix-equiv nfix natp))

(defun rfix-equiv (x y)
  (declare (type t x y))
  (equal (rfix x) (rfix y)))

(defthm rfix-rationalp
  (implies
   (rationalp x)
   (equal (rfix x) x)))

(defequiv rfix-equiv)

(defcong rfix-equiv equal (rfix x) 1)

(defthm rfix-equiv-rfix
  (rfix-equiv (rfix x) x))

(in-theory (disable rfix-equiv rfix rationalp))

(defun pair-p (x)
  (declare (type t x))
  (and (consp x)
       (natp (car x))
       (rationalp (cdr x))))

(defthm pair-p-implies
  (implies
   (pair-p x)
   (and (consp x)
        (natp (car x))
        (rationalp (cdr x))))
  :rule-classes (:forward-chaining))

(defthm implies-pair-p
  (implies
   (and (consp x)
        (natp (car x))
        (rationalp (cdr x)))
   (pair-p x))
  :rule-classes (:rewrite :type-prescription))

(def::un pair-fix (x)
  (declare (xargs :signature ((t) pair-p)))
  (if (consp x)
      (cons (nfix (car x)) (rfix (cdr x)))
    (cons 0 0)))

(defthm pair-fix-pair-p
  (implies
   (pair-p x)
   (equal (pair-fix x) x)))

(defun pair-equiv (x y)
  (declare (type t x y))
  (equal (pair-fix x)
         (pair-fix y)))

(defequiv pair-equiv)

(defcong pair-equiv equal (pair-fix x) 1)

(defthm pair-equiv-pair-fix
  (pair-equiv (pair-fix x) x))

(in-theory (disable pair-equiv pair-fix pair-p))

(def::und pair (varid coeff)
  (declare (xargs :signature ((natp rationalp) pair-p)
                  :congruence ((nfix-equiv rfix-equiv) equal)))
  (mbe :logic (cons (nfix varid) (rfix coeff))
       :exec (cons varid coeff)))

(def::signature pair (t t) pair-p
  :hints (("Goal" :in-theory (enable pair))))

(def::und pair-varid (x)
  (declare (xargs :signature ((pair-p) natp)
                  :congruence ((pair-equiv) equal)
                  :congruence-hints (("Goal" :in-theory (enable pair-fix pair-equiv)))))
  (mbe :logic (if (not (consp x)) 0 (nfix (car x)))
       :exec  (car x)))

(def::signature pair-varid (t) natp
  :hints (("Goal" :in-theory (enable pair-varid))))

(def::und pair-coeff (x)
  (declare (xargs :signature ((pair-p) rationalp)
                  :congruence ((pair-equiv) equal)
                  :congruence-hints (("Goal" :in-theory (enable pair-fix pair-equiv)))))
  (mbe :logic (if (not (consp x)) 0 (rfix (cdr x)))
       :exec  (cdr x)))

(def::signature pair-coeff (t) rationalp
  :hints (("Goal" :in-theory (enable pair-coeff))))

(def::un pair-value (x)
  (declare (xargs :signature ((pair-p) rationalp)
                  :congruence ((pair-equiv) equal)))
  (pair-coeff x))

(def::signature pair-value (t) rationalp
  :hints (("Goal" :in-theory (enable pair-value))))

(defthm pair-coeff-pair
  (equal (pair-coeff (pair x y))
         (rfix y))
  :hints (("Goal" :in-theory (enable pair pair-coeff))))

(defthm pair-varid-pair
  (equal (pair-varid (pair x y))
         (nfix x))
  :hints (("Goal" :in-theory (enable pair pair-varid))))

(in-theory (disable pair-value))

(defthm pair-equiv-reduction
  (iff (pair-equiv x y)
       (and (nfix-equiv (pair-varid x)
                        (pair-varid y))
            (rfix-equiv (pair-coeff x)
                        (pair-coeff y))))
  :hints (("Goal" :in-theory (enable pair-varid
                                     pair-coeff
                                     pair-equiv 
                                     pair-fix
                                     nfix-equiv
                                     rfix-equiv))))

(defun env-p (list)
  (declare (type t list))
  (if (not (consp list)) (null list)
    (and (pair-p (car list))
         (env-p (cdr list)))))

(defthm env-p-consp
  (implies
   (and
    (env-p list)
    (consp list))
   (and (pair-p (car list))
        (env-p (cdr list))))
  :rule-classes (:forward-chaining))

(def::un env-fix (list)
  (declare (xargs :signature ((t) env-p)))
  (if (not (consp list)) nil
    (cons (pair-fix (car list))
          (env-fix (cdr list)))))

(defthm len-env-fix
  (equal (len (env-fix list))
         (len list)))

(defun env-fix-equiv (x y)
  (declare (type t x y))
  (equal (env-fix x)
         (env-fix y)))

(defthm env-p-env-fix
  (implies
   (env-p x)
   (equal (env-fix x) x)))

(defequiv env-fix-equiv)

(defthm env-fix-equiv-env-fix
  (env-fix-equiv (env-fix x) x))

(defcong env-fix-equiv equal (env-fix x) 1)

(defcong env-fix-equiv env-fix-equiv (cdr x) 1)

(defcong env-fix-equiv equal (consp x) 1)

(defcong env-fix-equiv pair-equiv (car x) 1
  :hints (("Goal" :in-theory (e/d (pair-equiv) (PAIR-EQUIV-REDUCTION))
           :expand ((env-fix x) (env-fix x-equiv)))))

(in-theory (disable env-fix-equiv))

(defthm consp-env-fix
  (equal (consp (env-fix x))
         (consp x)))

(def::un get-binding (var env)
  (declare (xargs :signature ((t t) rationalp)
                  :congruence ((nfix-equiv env-fix-equiv) equal)
                  :congruence-hints (("Goal" :expand ((get-binding var env-equal) (get-binding var env))))
                  :measure (len env)))
  (let ((env (env-fix env))
        (var (nfix var)))
    (if (not (consp env)) 0
      (let ((pair (car env)))
        (if (nfix-equiv var (pair-varid pair))
            (pair-value pair)
          (get-binding var (cdr env)))))))

;; Introduce constants ..
(defun pterm-p (x)
  (declare (type t x))
  (or (rationalp x)
      (pair-p x)))

(defthm pterm-implication
  (implies
   (pterm-p x)
   (or (rationalp x)
       (pair-p x)))
  :rule-classes (:forward-chaining))

(defthm rational-implies-pterm
  (implies
   (rationalp x)
   (pterm-p x))
  :rule-classes (:rewrite :forward-chaining))

(defthm pair-implies-pterm
  (implies
   (pair-p x)
   (pterm-p x))
  :rule-classes (:rewrite :forward-chaining))

(def::un pterm-fix (x)
  (declare (xargs :signature ((t) pterm-p)))
  (if (pterm-p x) x
    (rfix x)))

(defthm pterm-implies-pterm-fix
  (implies
   (pterm-p x)
   (equal (pterm-fix x) x)))

(defthm pterm-fix-rational-reduction
  (implies
   (rationalp (pterm-fix x))
   (equal (pterm-fix x)
          (rfix x))))

(defthm pterm-fix-pair-reduction
  (implies
   (pair-p (pterm-fix x))
   (equal (pterm-fix x)
          (pair-fix x))))

(defun pterm-equiv (x y)
  (declare (type t x y))
  (equal (pterm-fix x)
         (pterm-fix y)))

(defequiv pterm-equiv)

(defcong pterm-equiv equal (pterm-fix x) 1)

(defthm pterm-equiv-pterm-fix
  (pterm-equiv (pterm-fix x) x))

(in-theory (disable pterm-equiv pterm-fix pterm-p))

(defun poly-p (list)
  (declare (type t list))
  (if (not (consp list)) (null list)
    (and (pterm-p (car list))
         (poly-p (cdr list)))))

(defthm env-implies-poly-p
  (implies
   (env-p list)
   (poly-p list))
  :rule-classes (:forward-chaining))

(defthm poly-p-append
  (implies
   (and
    (poly-p x)
    (poly-p y))
   (poly-p (append x y))))

(defthm poly-p-consp
  (implies
   (and
    (poly-p list)
    (consp list))
   (and (pterm-p (car list))
        (poly-p (cdr list))))
  :rule-classes (:forward-chaining))

(def::un poly-fix (list)
  (declare (xargs :signature ((t) poly-p)))
  (if (not (consp list)) nil
    (cons (pterm-fix (car list))
          (poly-fix (cdr list)))))

(defthm len-poly-fix
  (equal (len (poly-fix list))
         (len list))
  :rule-classes (:rewrite :linear))

(defthm consp-poly-fix
  (equal (consp (poly-fix x))
         (consp x)))

(defthm car-poly-fix
  (equal (car (poly-fix x))
         (if (not (consp x)) nil
           (pterm-fix (car x)))))

(defun poly-fix-equiv (x y)
  (declare (type t x y))
  (equal (poly-fix x)
         (poly-fix y)))

(defthm poly-p-poly-fix
  (implies
   (poly-p x)
   (equal (poly-fix x) x)))

(defequiv poly-fix-equiv)

(defthm poly-fix-equiv-poly-fix
  (poly-fix-equiv (poly-fix x) x))

(defcong poly-fix-equiv equal (poly-fix x) 1)

(defcong poly-fix-equiv poly-fix-equiv (cdr x) 1)

(defcong poly-fix-equiv equal (consp x) 1)

(defcong poly-fix-equiv pterm-equiv (car x) 1
  :hints (("Goal" :in-theory (e/d (pterm-equiv) (PAIR-EQUIV-REDUCTION))
           :expand ((poly-fix x) (poly-fix x-equiv)))))

(in-theory (disable poly-fix-equiv))

(def::un poly-eval (list env)
  (declare (xargs :signature ((t t) rationalp)
                  :measure (len list)
                  :congruence ((poly-fix-equiv env-fix-equiv) equal)))
  (let ((list (poly-fix list))
        (env  (env-fix  env)))
    (if (not (consp list)) 0
      (let ((pterm (pterm-fix (car list))))
        (if (rationalp pterm)
            (+ (rfix pterm) (poly-eval (cdr list) env))
          (let ((coef (pair-coeff pterm))
                (var  (pair-varid pterm)))
            (+ (* coef (get-binding var env))
               (poly-eval (cdr list) env))))))))

(def::un get-constant (poly)
  (declare (xargs :signature ((poly-p) rationalp)
                  :congruence ((poly-fix-equiv) equal)
                  :measure (len poly)))
  (let ((poly (poly-fix poly)))
    (if (not (consp poly)) 0
      (let ((pterm (car poly)))
        (if (rationalp pterm) (+ pterm (get-constant (cdr poly)))
          (get-constant (cdr poly)))))))

(defun pair-list-equiv (x y env)
  (declare (type t x y env))
  (let ((env (env-fix env))
        (x   (poly-fix x))
        (y   (poly-fix y)))
    (equal (poly-eval x env)
           (poly-eval y env))))

(defun-sk oompa-loompa (p1 p2)
  (exists (env) 
          (not (equal (poly-eval p1 env)
                      (poly-eval p2 env)))))

(defun pair-list-equivp (x y)
  (pair-list-equiv x y (oompa-loompa-witness x y)))

(defthm pair-list-equivp-implication
  (implies
   (pair-list-equivp p1 p2)
   (pair-list-equiv p1 p2 env))
  :hints (("Goal" :use oompa-loompa-suff)))

(def::un get-coeff (var poly)
  (declare (xargs :signature ((natp poly-p) rationalp)
                  :congruence ((nfix-equiv poly-fix-equiv) equal)
                  :measure (len poly)))
  (let ((poly (poly-fix poly)))
    (if (not (consp poly)) 0
      (let ((pterm (car poly)))
        (if (rationalp pterm) (get-coeff var (cdr poly))
          (if (nfix-equiv var (pair-varid pterm))
              (+ (pair-coeff pterm)
                 (get-coeff var (cdr poly)))
            (get-coeff var (cdr poly))))))))

(def::un drop-varid (varid poly)
  (declare (xargs :signature ((natp poly-p) poly-p)
                  :congruence ((nfix-equiv poly-fix-equiv) equal)
                  :measure (len poly)))
  (let ((poly (poly-fix poly)))
    (if (not (consp poly)) nil
      (let ((pterm (pterm-fix (car poly))))
        (if (rationalp pterm) (cons pterm (drop-varid varid (cdr poly)))
          (if (nfix-equiv varid (pair-varid pterm))
              (drop-varid varid (cdr poly))
            (cons pterm (drop-varid varid (cdr poly)))))))))

;; This is a key property ..
(defthmd alt-eval-poly
  (equal (poly-eval poly env)
         (+ (* (get-coeff varid poly) (get-binding varid env))
            (poly-eval (drop-varid varid poly) env)))
  :hints (("Goal" :induct (drop-varid varid poly))
          (and stable-under-simplificationp
               '(:expand ((POLY-EVAL POLY ENV)
                          (:free (varid) (GET-COEFF VARID POLY))
                          (:free (varid) (drop-varid VARID POLY)))))
          ))

(def::un zeroize-varid (varid env)
  (declare (xargs :signature ((natp env-p) env-p)
                  :congruence ((nfix-equiv env-fix-equiv) equal)
                  :measure (len env)))
  (let ((env (env-fix env)))
    (if (not (consp env)) nil
      (let ((pair (car env)))
        (if (nfix-equiv varid (pair-varid pair))
            (zeroize-varid varid (cdr env))
          (cons (pair-fix pair)
                (zeroize-varid varid (cdr env))))))))

(defthm get-binding-zeroize
  (equal (get-binding vid1 (zeroize-varid vid2 env))
         (if (nfix-equiv vid1 vid2) 0
           (get-binding vid1 env)))
  :hints (("Goal" :induct (zeroize-varid vid2 env)
           :expand (
                    (:free (vid) (get-binding vid env))
                    (:free (vid) (zeroize-varid vid env))))))

(defcong pair-equiv env-fix-equiv (cons a lst) 1
  :hints (("Goal" :in-theory (e/d (env-fix-equiv)
                                  (pair-equiv-reduction)))))

(defcong env-fix-equiv env-fix-equiv (cons a lst) 2
  :hints (("Goal" :in-theory (enable env-fix-equiv))))

(encapsulate
    ()

  (local
   (defthm this-is-more-like-it
     (equal (poly-eval poly (cons pair env))
            (+ (* (pair-value pair) (get-coeff (pair-varid pair) poly))
               (poly-eval poly (zeroize-varid (pair-varid pair) env))))))
  
  (defthm poly-eval-consp-env
    (implies
     (consp env)
     (equal (poly-eval poly env)
            (let ((pair (car env))
                  (env   (cdr env)))
              (+ (* (pair-value pair) (get-coeff (pair-varid pair) poly))
                 (poly-eval poly (zeroize-varid (pair-varid pair) env))))))
    :hints (("Goal" :use (:instance this-is-more-like-it
                                    (pair (car env))
                                    (env   (cdr env))))))

  )

(defthm get-constant-drop-varid
  (equal (get-constant (drop-varid varid poly))
         (get-constant poly)))

(def::un zeroize-constant (poly)
  (declare (xargs :signature ((poly-p) env-p)
                  :congruence ((poly-fix-equiv) equal)
                  :measure (len poly)))
  (let ((poly (poly-fix poly)))
    (if (not (consp poly)) nil
      (let ((pterm (pterm-fix (car poly))))
        (if (rationalp pterm) (zeroize-constant (cdr poly))
          (cons pterm (zeroize-constant (cdr poly))))))))

(defthm len-zeroize-constant
  (<= (len (zeroize-constant poly))
      (len poly))
  :rule-classes :linear)

(defthm poly-eval-zeroize-constant
  (equal (poly-eval (zeroize-constant poly) env)
         (+ (poly-eval poly env)
            (- (get-constant poly)))))

(defthm get-constant-zeroize-constant
  (equal (get-constant (zeroize-constant poly))
         0))

(defthm poly-eval-consp-not-consp-env
  (implies
   (not (consp env))
   (equal (poly-eval poly env) 
          (get-constant poly))))

(defthm drop-varid-to-zeroize-varid
  (equal (poly-eval (drop-varid varid poly) env)
         (poly-eval poly (zeroize-varid varid env)))
  :hints (("Goal" :induct (drop-varid varid poly)
           :do-not-induct t
           :expand ((:free (env) (poly-eval poly env))
                    (:free (vid) (drop-varid vid poly))))))

(defthm len-drop-varid
  (<= (len (drop-varid varid p1))
      (len p1))
  :rule-classes :linear)

(def::un zerop-poly (p1)
  (declare (xargs :measure (len p1)
                  :congruence ((poly-fix-equiv) equal)
                  :congruence-hints (("Goal" :expand ((zerop-poly p1)
                                                      (zerop-poly p1-equal)
                                                      )))))
  (let ((p1 (poly-fix p1)))
    (if (not (consp p1)) t
      (let ((pterm (car p1)))
        (if (rationalp pterm) (zerop-poly (zeroize-constant (cdr p1)))
          (let ((varid (pair-varid pterm)))
            (and (equal (get-coeff varid p1) 0)
                 (zerop-poly (drop-varid varid (cdr p1))))))))))

(def::un coeff-equiv (p1 p2)
  (declare (xargs :measure (len p1)
                  :congruence ((poly-fix-equiv poly-fix-equiv) equal)
                  :congruence-hints (("Goal" :expand ((coeff-equiv p1 p2-equal)
                                                      (coeff-equiv p1 p2)
                                                      (coeff-equiv p1-equal p2))))
                  ))
  (let ((p1 (poly-fix p1))
        (p2 (poly-fix p2)))
    (if (not (consp p1)) (zerop-poly p2)
      (let ((pterm (car p1)))
        (if (rationalp pterm) (coeff-equiv (cdr p1) p2)
          (let ((varid (pair-varid pterm)))
            (and (equal (get-coeff varid p1)
                        (get-coeff varid p2))
                 (coeff-equiv (drop-varid varid (cdr p1))
                              (drop-varid varid p2)))))))))

(defthmd open-poly-eval
  (implies
   (consp poly)
   (equal (poly-eval poly env)
          (let ((pterm (pterm-fix (car poly))))
            (if (rationalp pterm) (+ (get-constant poly)
                                     (poly-eval (zeroize-constant (cdr poly)) env))
              (let ((varid (pair-varid pterm)))
                (+ (* (get-coeff varid poly) (get-binding varid env))
                   (poly-eval (drop-varid varid poly) env)))))))
  :hints (("Goal" :do-not-induct t)
          ("Subgoal 2" :expand ((GET-CONSTANT POLY) (poly-eval poly env)))
          ("Subgoal 1" :use (:instance alt-eval-poly
                                       (varid (pair-varid (car poly)))))))

(defthmd open-poly-eval-2
  (implies
   (and
    (consp p1)
    (syntaxp (equal p1 'p1))
    (syntaxp (equal p2 'p2)))
   (equal (poly-eval p2 env)
          (let ((pterm (pterm-fix (car p1))))
            (if (rationalp pterm) (+ (get-constant p2)
                                     (poly-eval (zeroize-constant p2) env))
              (let ((varid (pair-varid pterm)))
                (+ (* (get-coeff varid p2) (get-binding varid env))
                   (poly-eval (drop-varid varid p2) env)))))))
  :hints (("Goal" :do-not-induct t)
          ("Subgoal 1" :use (:instance alt-eval-poly
                                       (poly p2)
                                       (varid (pair-varid (car p1)))))))

(defthm poly-eval-not-consp
  (implies 
   (not (consp p1))
   (equal (poly-eval p1 env) 0)))

(in-theory (disable poly-fix poly-eval drop-varid-to-zeroize-varid))

;; You need poly-eval to open up with a drop-varid
(defthm poly-eval-zerop-poly
  (implies
   (zerop-poly p1)
   (equal (poly-eval p1 env) 
          (get-constant p1)))
  :hints (("Goal" :in-theory (e/d (open-poly-eval)
                                  (poly-eval-zeroize-constant))
           :induct (zerop-poly p1)
           :expand ((GET-CONSTANT P1) (:free (x) (DROP-VARID x P1)))
           :do-not-induct t)))

#+joe
(defthm poly-eval-coeff-poly
  (implies
   (coeff-equiv p1 p2)
   (equal (- (poly-eval p1 env) (poly-eval p2 env))
          (- (get-constant p1) (get-constant p2))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (open-poly-eval open-poly-eval-2)
                           (poly-eval-zeroize-constant))
           :expand ((:free (x) (DROP-VARID x P1)))
           :induct (coeff-equiv p1 p2)
           :do-not-induct t)
          ("Subgoal *1/2" :in-theory (enable POLY-EVAL-ZEROIZE-CONSTANT))))

(in-theory (disable PAIR-EQUIV-REDUCTION open-poly-eval poly-eval-consp-env))

(def::und plus (p1 p2)
  (declare (xargs :signature ((t t) poly-p)
                  :congruence ((poly-fix-equiv poly-fix-equiv) equal)))
  (let ((p1 (poly-fix p1))
        (p2 (poly-fix p2)))
    (append p1 p2)))

(def::und add1 (pterm p2)
  (declare (xargs :signature ((pterm-p poly-p) poly-p)
                  :congruence ((pterm-equiv poly-fix-equiv) equal)))
  (let ((pterm (pterm-fix pterm))
        (p2    (poly-fix p2)))
    (cons pterm p2)))

(defthm poly-eval-cons
  (equal (poly-eval (cons a list) env)
         (let ((a (pterm-fix a)))
           (if (rationalp a) (+ a (poly-eval list env))
             (+ (* (pair-coeff a) (get-binding (pair-varid a) env))
                (poly-eval list env)))))
  :hints (("Goal" :do-not-induct t
           :expand (POLY-EVAL (CONS A LIST) ENV))))

(defthm poly-eval-add1
  (equal (poly-eval (add1 a list) env)
         (let ((a (pterm-fix a)))
           (if (rationalp a) (+ a (poly-eval list env))
             (+ (* (pair-coeff a) (get-binding (pair-varid a) env))
                (poly-eval list env)))))
  :hints (("Goal" :in-theory (enable add1))))

(defthm poly-eval-plus
  (equal (poly-eval (plus p1 p2) env)
         (+ (poly-eval p1 env)
            (poly-eval p2 env)))
  :hints (("Goal" :in-theory (enable poly-fix plus))))

(defthm cdr-poly-fix
  (equal (cdr (poly-fix x))
         (poly-fix (cdr x)))
  :hints (("Goal" :in-theory (enable poly-fix))))

(def::un mul (c poly)
  (declare (xargs :signature ((t t) poly-p)
                  :measure (len poly)
                  :congruence ((rfix-equiv poly-fix-equiv) equal)))
  (let ((poly (poly-fix poly))
        (c    (rfix c)))
    (if (not (consp poly)) nil
      (let ((pterm (pterm-fix (car poly))))
        (if (rationalp pterm) (cons (* c pterm) (mul c (cdr poly)))
          (cons (pair (pair-varid pterm) (* c (pair-coeff pterm)))
                (mul c (cdr poly))))))))

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm poly-eval-mul
    (equal (poly-eval (mul c poly) env)
           (* (rfix c) (poly-eval poly env)))
    :hints (("Goal" :in-theory (enable poly-eval))))

  )

(def::und sub (p1 p2)
  (declare (xargs :signature ((t t) poly-p)
                  :congruence ((poly-fix-equiv poly-fix-equiv) equal)))
  (let ((p2 (mul -1 p2)))
    (plus p1 p2)))

(defthm poly-eval-sub
  (equal (poly-eval (sub p1 p2) env)
         (- (poly-eval p1 env)
            (poly-eval p2 env)))
  :hints (("Goal" :in-theory (enable sub))))

(defthm get-constant-sub
  (equal (get-constant (sub p1 p2))
         (- (get-constant p1)
            (get-constant p2)))
  :hints (("Goal" :in-theory (enable plus sub))))

(defun non-zero-coefficient (varid poly)
  (not (equal (get-coeff varid poly) 0)))

;; What you should really have is a symbolic
;; binding.  In other words, you should support
;; beta reduction.  You could even arrange it so
;; that the evaluation process "popped" the
;; enviornment .. which would give you a
;; termination argumnet.

;;
(defund bool-fix (x)
  (declare (type t x))
  (if x t nil))

;; (defun one-var-poly-p (x)
;;   (declare (type t x))
;;   (and (consp x)
;;        (let ((pair (car x)))
;;          (and
;;           (pair-p pair)
;;           (equal (pair-coeff pair) 1)))))

;; (def::und varid-of-one-var-poly (x)
;;   (declare (xargs :signature ((one-var-poly-p) natp)))
;;   (let ((pair (car x)))
;;     (pair-varid pair)))
  
;; =========================================

;; So variables are expressed as polynomials.
(def::und eval-ineq (term env)
  (declare (xargs :signature ((t t) booleanp)
                  :congruence ((nil env-fix-equiv) equal)))
  (case-match term
    (('and x y)
     (let ((x (eval-ineq x env))
           (y (eval-ineq y env)))
       (and x y)))
    (('or x y)
     (let ((x (eval-ineq x env))
           (y (eval-ineq y env)))
       (or x y)))
    (('not x)
     (let ((x (eval-ineq x env)))
       (not x)))
    (('= var poly)
     (let ((x (get-binding var env))
           (y (poly-eval poly env)))
       (equal x y)))
    (('!= var poly)
     (let ((x (get-binding var env))
           (y (poly-eval poly env)))
       (not (equal x y))))
    (('< x y)
     (let ((x (get-binding x env))
           (y (poly-eval y env)))
       (< x y)))
    (('<= x y)
     (let ((x (get-binding x env))
           (y (poly-eval y env)))
       (<= x y)))
    (('> x y)
     (let ((x (get-binding x env))
           (y (poly-eval y env)))
       (> x y)))
    (('>= x y)
     (let ((x (get-binding x env))
           (y (poly-eval y env)))
       (>= x y)))
    (& nil)))

;; (eval-ineq (acons 1 2 (acons 2 3 nil)) (acons 1 2 (acons 2 3 nil)))

(include-book "arithmetic-5/top" :dir :system)

;; Hmm .. not a very generous equivalence ..
(defthm open-poly-fix-equiv
  (implies
   (consp x)
   (equal (poly-fix-equiv x y)
          (and (consp y)
               (pterm-equiv (car x) (car y))
               (poly-fix-equiv (cdr x) (cdr y)))))
  :hints (("Goal" :in-theory (enable pterm-equiv poly-fix poly-fix-equiv))))

(defun dual-induction (x y)
  (if (and (consp x) (consp y))
      (dual-induction (cdr x) (cdr y))
    (cons x y)))

(defcong poly-fix-equiv poly-fix-equiv (append x y) 1
  :hints (("Goal" :induct (dual-induction x x-equiv))))

(defthm get-coeff-append
  (equal (get-coeff varid (append x y))
         (+ (get-coeff varid x)
            (get-coeff varid y))))

(defthm get-constant-append
  (equal (get-constant (append x y))
         (+ (get-constant x)
            (get-constant y))))

;; (def::un not-const-rec (poly pre)
;;   (declare (xargs :signature ((poly-p poly-p) booleanp)))
;;   (if (not (consp poly)) nil
;;     (let ((pair (car poly)))
;;       (let ((varid (pair-varid pair)))
;;         (let ((c (get-coeff varid (append pre poly))))
;;           (if (not (zerop c)) t
;;             (not-const-rec (cdr poly) (cons pair pre))))))))

;; (def::un find-non-zero-varid-rec (poly pre)
;;   (declare (xargs :signature ((poly-p poly-p) natp)))
;;   (if (not (consp poly)) 0
;;     (let ((pair (car poly)))
;;       (let ((varid (pair-varid pair)))
;;         (let ((c (get-coeff varid (append pre poly))))
;;           (if (not (zerop c)) varid
;;             (find-non-zero-varid-rec (cdr poly) (cons pair pre))))))))

;; (def::und not-constp (poly)
;;   (declare (xargs :signature ((t) booleanp)))
;;   (and (poly-p poly)
;;        (not-const-rec poly nil)))

;; (def::und find-non-zero-varid (poly)
;;   (declare (xargs :signature ((poly-p) natp)))
;;   (find-non-zero-varid-rec poly nil))

(def::un alt-not-constp (poly)
  (declare (xargs :signature ((poly-p) booleanp)
                  :congruence ((poly-fix-equiv) equal)
                  :congruence-hints (("Goal" :expand ((alt-not-constp poly)
                                                      (alt-not-constp poly-equal))))
                  :measure (len poly)))
  (let ((poly (poly-fix poly)))
    (if (endp poly) nil
      (let ((pterm (pterm-fix (car poly))))
        (if (rationalp pterm) (alt-not-constp (cdr poly))
          (let ((varid (pair-varid pterm)))
            (let ((coeff (get-coeff varid poly)))
              (or (not (zerop coeff))
                  (alt-not-constp (drop-varid varid (cdr poly)))))))))))

(defund not-constp (poly)
  (declare (type t poly))
  (and (poly-p poly)
       (alt-not-constp poly)))

(defun isConstant (poly)
  (declare (type (satisfies poly-p) poly))
  (not (not-constp poly)))

(defthm not-constp-type
  (implies
   (not-constp poly)
   (poly-p poly))
  :hints (("Goal" :in-theory (enable not-constp)))
  :rule-classes (:forward-chaining))

(defthm not-not-constp
  (implies
   (and
    (not (not-constp poly))
    (poly-p poly))
   (not (alt-not-constp poly)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable not-constp))))

(defthm poly-eval-const-poly
  (implies
   (not (alt-not-constp poly))
   (equal (poly-eval poly env)
          (get-constant poly)))
  :hints (("Goal" :in-theory (enable get-constant open-poly-eval))))

(def::un find-non-zero-varid (poly)
  (declare (xargs :signature ((poly-p) natp)
                  :congruence ((poly-fix-equiv) equal)
                  :congruence-hints (("Goal" :expand ((find-non-zero-varid poly)
                                                      (find-non-zero-varid poly-equal))))
                  :measure (len poly)))
  (let ((poly (poly-fix poly)))
    (if (endp poly) 0
      (let ((pterm (pterm-fix (car poly))))
        (if (rationalp pterm) (find-non-zero-varid (cdr poly))
          (let ((varid (pair-varid pterm)))
            (let ((coeff (get-coeff varid poly)))
              (if (not (zerop coeff)) varid
                (find-non-zero-varid (drop-varid varid (cdr poly)))))))))))
  
(defthm nfix-equiv-to-equal
  (implies
   (and
    (natp x)
    (natp y))
   (equal (nfix-equiv x y)
          (equal x y)))
  :hints (("Goal" :in-theory (enable nfix-equiv))))

(defthm get-coeff-drop-varid
  (equal (get-coeff x (drop-varid y poly))
         (if (nfix-equiv x y) 0
           (get-coeff x poly))))

(defthm drop-varid-commute
  (equal (drop-varid x (drop-varid y poly))
         (drop-varid y (drop-varid x poly))))

(defthm get-coeff-mul
  (equal (get-coeff varid (mul c poly))
         (* (rfix c) (get-coeff varid poly))))

(defthm get-coeff-plus
  (equal (get-coeff id (plus x y))
         (+ (get-coeff id x)
            (get-coeff id y)))
  :hints (("Goal" :in-theory (enable get-coeff plus))))

(defthmd get-coeff-sub
  (equal (get-coeff var (sub a b))
         (- (get-coeff var a) (get-coeff var b)))
  :hints (("Goal" :in-theory (enable get-coeff sub))))

(defthm mul-drop-varid
  (equal (mul c (drop-varid varid poly))
         (drop-varid varid (mul c poly))))

(encapsulate
    ()

  (local
   (defthm find-non-zero-varid-works-when-not-constp
     (implies
      (alt-not-constp poly)
      (not (equal (get-coeff (find-non-zero-varid poly) poly) 0)))
     :hints (("Goal" :induct (alt-not-constp poly)
              :expand (FIND-NON-ZERO-VARID POLY)
              :do-not-induct t))
     :rule-classes ((:forward-chaining :trigger-terms ((find-non-zero-varid poly))))))

  (defthm find-non-zero-varid-works
    (implies
     (not-constp poly)
     (not (equal (get-coeff (find-non-zero-varid poly) poly) 0)))
    :hints (("Goal" :in-theory (enable not-constp)))
    :rule-classes ((:forward-chaining :trigger-terms ((find-non-zero-varid poly)))))

  (local
   (defthm weaker-alt-not-constp
     (implies
      (NOT (ALT-NOT-CONSTP poly))
      (not (alt-not-constp (drop-varid x poly))))
     :hints (("Goal" :expand (:free (a poly) (alt-not-constp (cons a poly)))))))

  (local
   (defthm alt-not-constp-mul-1
     (implies
      (rfix-equiv c 0)
      (not (alt-not-constp (mul c poly))))))
   
  (local
   (defthm work-harder
     (implies
      (and
       (rationalp c)
       (rationalp x)
       (rationalp y))
      (iff (equal (+ (* c x) (* c y)) 0)
           (or (equal c 0)
               (equal (+ x y) 0))))))

  (local
   (defthm alt-not-constp-mul-2
     (implies
      (not (rfix-equiv c 0))
      (iff (alt-not-constp (mul c poly))
           (alt-not-constp poly)))
     :hints (("Goal" :induct (alt-not-constp poly)
              :do-not-induct t
              :expand (mul c poly)
              :in-theory (enable rfix-equiv)))))

  (defthm not-constp-mul
    (iff (not-constp (mul c poly))
         (if (rfix-equiv c 0) nil
           (not-constp (poly-fix poly))))
    :hints (("Goal" :do-not-induct t
             :in-theory (enable not-constp)
             :cases ((rfix-equiv c 0)))))
  
  (defthm find-non-zero-varid-mul
    (implies
     (not (rfix-equiv c 0))
     (equal (find-non-zero-varid (mul c poly))
            (find-non-zero-varid poly)))
    :hints (("Goal" :expand (mul c poly)
             :in-theory (enable rfix-equiv)
             :induct (find-non-zero-varid poly))))
   
  )
  
;;(defthm 
;;  (equal (mv-nth 0 (find-non-zero-varid (plus x y)))
;;         (not (equal (get-coeff (nth 1 (find-non-zero-varid poly)) poly) 0))))

(include-book "coi/util/in-conclusion" :dir :system)

(in-theory (disable mv-nth-to-val mv-nth))

(defund stop-forward (x)
  (declare (ignore x))
  t)

(in-theory (disable (:type-prescription stop-forward)))

(defund forward-wrapper (x)
  x)

(set-state-ok t)

(defun not-in-conclusion-check-fn (top fn args mfc state)
  (declare (ignore state)
           (type t args))
  (if (not (acl2::mfc-ancestors mfc))
      (let ((args (delist args)))
        (let ((clause (mfc-clause mfc)))
          (if (if (not top) (appears-in-clause fn args nil clause)
                (if (and (equal fn 'not)
                         (consp args))
                    (member-of-clause :negated (car args) clause)
                  (member-of-clause top (cons fn args) clause)))
              nil
            (list (cons 'not-in-conclusion-free-variable `(quote t))))))
    nil))

(defmacro not-in-conclusion-check (term &key (top 'nil))
  (declare (xargs :guard (consp term)))
  `(and
    (equal not-in-conclusion-check-term (list ,@(cdr term)))
    (bind-free (not-in-conclusion-check-fn ,top ',(car term) not-in-conclusion-check-term acl2::mfc acl2::state)
               (not-in-conclusion-free-variable))))

(defthm forward-wrapper-to-stop-forward
  (implies
   (in-conclusion-check (forward-wrapper (hide term)) :top t)
   (equal (forward-wrapper (hide term))
          (and (stop-forward (hide term)) term)))
  :hints (("Goal" :expand (:free (x) (hide x))
           :in-theory (enable forward-wrapper stop-forward))))

(defmacro defthm-> (name term)
  (case-match term
    (('implies hyp conc)
     `(defthm ,name
        (implies
         (and
          (in-conclusion-check ,hyp :top t)
          (not-in-conclusion-check (stop-forward (hide ,hyp)) :top t))
         (iff ,hyp (and (forward-wrapper (hide ,hyp)) ,conc)))
        :hints (("Goal" :expand (:free (x) (hide x))
                 :in-theory (enable forward-wrapper)))))
    (t nil)))

(defthm-> find-non-zero-varid-forward
  (implies
   (not-constp poly)
   (not (equal (get-coeff (find-non-zero-varid poly) poly) 0))))

(include-book "coi/util/skip-rewrite" :dir :system)

(in-theory (disable find-non-zero-varid-works))

(in-theory (disable (:REWRITE MV-NTH-TO-VAL) mv-nth))

(defun tri-p (x)
  (declare (type t x))
  (or (equal x 1)
      (equal x -1)
      (equal x 0)))

(in-theory (disable tri-p))

(defun non-zerop (x)
  (declare (type t x))
  (and (integerp x)
       (not (equal x 0))))

;; ============================================================

;; (< (+ ax by cz) 0)
;; (< (+ ax by)  -cz)
;; (< (+ ax by)  -cz)

(def::und solve (varid poly)
  (declare (xargs :signature ((natp poly-p) poly-p)
                  :congruence ((nfix-equiv poly-fix-equiv) equal)))
  (let ((c (get-coeff varid poly)))
    (if (zerop c) nil
      (let ((c (- c)))
        (let ((poly (add1 (pair varid c) poly)))
          (mul (/ c) poly))))))

;;    x
;;
;; v --
;;
;;    y

(defthm <-solve-when-<-coeff
  (implies
   (and
    (< (poly-eval poly env) 0)
    (< (get-coeff varid poly) 0))
   (< (poly-eval (solve varid poly) env) (get-binding varid env)))
  :hints (("Goal" :in-theory (enable solve)
           :do-not-induct t)))

(defthm <-solve-when-<-coeff-alt
  (implies
   (and
    (< 0 (poly-eval poly env))
    (< 0 (get-coeff varid poly)))
   (< (poly-eval (solve varid poly) env) (get-binding varid env)))
  :hints (("Goal" :in-theory (enable solve)
           :do-not-induct t)))

(defthm <=-solve-when-<-coeff
  (implies
   (and
    (<= 0 (poly-eval poly env))
    (< (get-coeff varid poly) 0))
   (<= (get-binding varid env) (poly-eval (solve varid poly) env)))
  :hints (("Goal" :in-theory (enable solve)
           :do-not-induct t)))

(defthm <=-solve-when-<-coeff-alt
  (implies
   (and
    (>= 0 (poly-eval poly env))
    (> (get-coeff varid poly) 0))
   (<= (get-binding varid env) (poly-eval (solve varid poly) env)))
  :hints (("Goal" :in-theory (enable solve)
           :do-not-induct t)))

(defthm >-solve-when->-coeff-z
  (implies
   (and
    (< 0 (poly-eval poly env))
    (> 0 (get-coeff varid poly)))
   (< (get-binding varid env) (poly-eval (solve varid poly) env)))
  :hints (("Goal" :in-theory (enable solve)
           :do-not-induct t)))

(defthm =-solve-when-nz-coeff
  (implies
   (and
    (= (poly-eval poly env) 0)
    (force (not (= 0 (get-coeff varid poly)))))
   (= (poly-eval (solve varid poly) env) (get-binding varid env)))
  :hints (("Goal" :in-theory (enable solve)
           :do-not-induct t)))

(defthm >-solve-when->-coeff
  (implies
   (and
    (> 0 (poly-eval poly env))
    (force (< 0 (get-coeff varid poly))))
   (< (get-binding varid env) (poly-eval (solve varid poly) env)))
  :hints (("Goal" :in-theory (enable solve)
           :do-not-induct t)))

(defthm >-solve-when-<-coeff
  (implies
   (and
    (not (> 0 (poly-eval poly env)))
    (< 0 (get-coeff varid poly)))
   (not (< (get-binding varid env) (poly-eval (solve varid poly) env))))
  :hints (("Goal" :in-theory (enable solve)
           :do-not-induct t)))

(defthm >-solve-when-<-coeff-alt
  (implies
   (and
    (not (< 0 (poly-eval poly env)))
    (> 0 (get-coeff varid poly)))
   (not (< (get-binding varid env) (poly-eval (solve varid poly) env))))
  :hints (("Goal" :in-theory (enable solve)
           :do-not-induct t)))

(defthm the-equality-meaning-of-solve
  (implies
   (not-constp poly)
   (iff (equal (get-binding (find-non-zero-varid poly) any)
               (poly-eval (solve (find-non-zero-varid poly) poly) any))
        (equal (poly-eval poly any) 0)))
  :hints (("Goal" :in-theory (enable solve)
           :do-not-induct t)))

(defthm poly-eval-const-difference
  (implies
   (not (not-constp (sub p1 p2)))
   (equal (poly-eval p1 any)
          (+ (poly-eval p2 any)
             (get-constant p1)
             (- (get-constant p2)))))
  :hints (("Goal" :do-not-induct t
           :use (:instance poly-eval-sub
                           (env any)))))

(defthm not-constp-mul-type
  (implies
   (and
    (not-constp poly)
    (poly-p poly)
    (not (rfix-equiv c 0)))
   (not-constp (mul c poly)))
  :rule-classes (:forward-chaining))

(def::un simplify-poly (poly)
  (declare (xargs :signature ((poly-p) poly-p)
                  :measure (len poly)))
  (if (endp poly) nil
    (let ((pterm (car poly)))
      (if (rationalp pterm)
          (let ((const (get-constant poly)))
            (if (= const 0) (simplify-poly (zeroize-constant (cdr poly)))
              (cons const (simplify-poly (zeroize-constant (cdr poly))))))
        (let ((varid (pair-varid pterm)))
          (let ((coeff (get-coeff varid poly)))
            (if (= coeff 0) (simplify-poly (drop-varid varid (cdr poly)))
              (cons (pair varid (get-coeff varid poly))
                    (simplify-poly (drop-varid varid (cdr poly)))))))))))

#+joe
(defthm simplify-poly-idempotent
  (equal (eval-poly (simplify-poly poly) env)
         (eval-poly poly env)))

(def::und poly-lcm (poly)
  (declare (ignore poly)
           (xargs :signature ((poly-p) natp)))
  0)
