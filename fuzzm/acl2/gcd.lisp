(in-package "ACL2")
#|
(defmacro met (bind &rest body)
  `(mv-let ,(car bind) ,(cadr bind)
	   ,@body))

(defun div (n d)
  (/ n d))

(encapsulate
    (
     ((nat-egcd * *) => (mv * * *))
     ((divisiblep * *) => *)
     )

  (local (include-book "arithmetic/mod-gcd" :dir :system))

  (local
   (in-theory (disable
               nonneg-int-gcd
               nonneg-int-gcd-multiplier1
               nonneg-int-gcd-multiplier2
               )))

  (local 
   (defun nat-egcd (a b)
     (mv (nonneg-int-gcd a b)
         (nonneg-int-gcd-multiplier1 a b)
         (nonneg-int-gcd-multiplier2 a b))))

  (local 
   (defun divisiblep (d n)
     (equal (nonneg-int-mod n d) 0)))

  (defthm nat-egcd-signature
    (and (natp (mv-nth 0 (nat-egcd a b)))
         (integerp (mv-nth 1 (nat-egcd a b)))
         (integerp (mv-nth 2 (nat-egcd a b))))
    :rule-classes ((:forward-chaining :trigger-terms ((nat-egcd a b)))))

  (defthmd nat-egcd-property
    (implies
     (and
      (natp p)
      (natp d)
      (< 0 p)
      (< 0 d))
     (met ((g z s) (nat-egcd d p))
       (equal g (+ (* z d) (* s p)))))
    :hints (("Goal" :in-theory (enable Linear-combination-for-nonneg-int-gcd))))

  (defthm divisibility-implication
    (implies
     (and
      (integerp n)
      (integerp d)
      (<= 0 n)
      (< 0 d)
      (divisiblep d n))
     (integerp (div n d)))
    :hints (("Goal" :use (:instance
                          divides-when-nonneg-int-mod-0))))
                          

  )



(implies
 (and
  (divisiblep (mv-nth 0 (nat-egcd A B)) z)
  )
 (equal (* A x) (+ (* B y) z))


(forall (y,z)
        (exists (x)
                (and (integerp x)
                     (equal (* A x) (+ (* B y) z)))))

(defun type-safe-bindings (env)
  (if (not (consp env)) t
    (let ((entry (car env)))
      (and (if (integer-type (bound-variable entry))
               (integerp (bound-value entry))
             (rationalp (bound-value entry)))
           (type-safe-bindings (cdr env))))))

(defthm 
  (implies
   (and
    (type-safe-bindings env)
    (integer-type var))
   (integerp (get-binding var env))))

(defun integer-typed-variables (env)
  (if (not (consp env)) t
    (let ((entry (car env)))
      (and (integer-type (bound-variable entry))
           (integer-typed-variables (cdr env))))))

(defun type-ordered-variables (env)
  (if (not (consp env)) t
    (let ((entry (car env)))
      (if (integer-type (bound-variable entry))
          (integer-typed-variables env)
        (type-ordered-variables (cdr env))))))

(defstub integer-polyp (poly) nil)


(

(defthm
  (implies
   (and
    (integer-polyp poly)
    (type-safe-bindings env))
   (integerp (eval-poly poly env))))

(defstub eval-poly (poly env) nil)

(let ((lower (eval-poly (constraint-lower constraint) env))
      (upper (eval-poly (constraint-upper constraint) env)))
  (interval-choice (constraint-type constraint) lower upper))
|#
;; start here
(include-book "order")
(include-book "coi/util/defun" :dir :system)

(defthm rfix-rationalp
  (implies
   (rationalp x)
   (equal (rfix x) x)))

(defun requiv (x y)
  (declare (type t x y))
  (equal (rfix x) (rfix y)))

(defequiv requiv)

(defthm requiv-rfix
  (requiv (rfix x) x))

(defcong requiv equal (rfix x) 1)

(in-theory (disable rfix requiv))

(defund get-binding (index env)
  (let ((v (assoc index env)))
    (if (not v) 0 (rfix (cdr v)))))

(defthm get-binding-cons
  (equal (get-binding index (cons (cons index value) alist))
         (rfix value))
  :hints (("Goal" :in-theory (enable get-binding))))

(defstub eval-poly (poly env) nil)

(defstub constraint-lower (c) nil)
(defstub constraint-upper (c) nil)
(defstub constraint-op (c) nil)
(defstub constraint-var (c) nil)

(defstub var-type (var) nil)
(def::und var-index (var)
  (declare (ignore var) (xargs :signature ((t) prat-p)))
  2)

(defund linear-p (type op value lower upper)
  (declare (ignore type op lower upper))
  (< 0 (rfix value)))

(defcong requiv equal (linear-p type op value lower upper) 3
  :hints (("Goal" :in-theory (enable linear-p))))

(defund value-satisfies-constraint (value constraint env)
  (let ((value (rfix value)))
    (let ((var (constraint-var constraint)))
      (let ((lower (eval-poly (constraint-lower constraint) env))
            (upper (eval-poly (constraint-upper constraint) env)))
        (linear-p (var-type var) (constraint-op constraint) value lower upper)))))

(defcong requiv equal (value-satisfies-constraint value constraint env) 1
  :hints (("Goal" :in-theory (enable value-satisfies-constraint))))

(defund eval-constraint (constraint env)
  (let ((value (get-binding (var-index (constraint-var constraint)) env)))
    (value-satisfies-constraint value constraint env)))

(defun zoid-indicies (zoid)
  (if (not (consp zoid)) nil
    (let ((constrint (car zoid)))
      (cons (var-index (constraint-var constrint)) (zoid-indicies (cdr zoid))))))

(defun wf-zoid (zoid)
  (declare (type t zoid))
  (and (ec-call (>-ordered-p (ec-call (zoid-indicies zoid))))
       ))

(defthm open-wf-zoid
  (implies
   (consp zoid)
   (equal (wf-zoid zoid)
          (let ((constraint (car zoid)))
            (and (>-all (var-index (constraint-var constraint))
                        (zoid-indicies (cdr zoid)))
                 (wf-zoid (cdr zoid)))))))

(in-theory (disable wf-zoid))

(defun eval-zoid (zoid env)
  (if (not (consp zoid)) t
    (and (eval-constraint (car zoid) env)
         (eval-zoid (cdr zoid) env))))

(skip-proofs
(defthm eval-constraint-ignore-binding
  (implies
   (and
    (prat-p var)
    (< (var-index (constraint-var constraint)) var))
   (equal (eval-constraint constraint (cons (cons var value) env))
          (eval-constraint constraint env)))))

(defun zoid-order (zoid)
  (if (not (consp zoid)) 0
    (var-index (constraint-var (car zoid)))))

(defthm gt-zoid-order-from-gt-all
  (implies
   (and
    (prat-p x)
    (>-all x (zoid-indicies zoid)))
   (> x (zoid-order zoid)))
  :rule-classes (:linear))

(defthm eval-zoid-ignore-binding
  (implies
   (and
    (wf-zoid zoid)
    (prat-p var)
    (< (zoid-order zoid) var))
   (equal (eval-zoid zoid (cons (cons var value) env))
          (eval-zoid zoid env))))

(in-theory (disable zoid-order))

(defchoose choose-satisfying-value (value) (constraint env)
  (value-satisfies-constraint value constraint env))

(skip-proofs
(defthm env-reduction-2
  (implies
   (equal index (var-index (constraint-var constraint)))
   (iff (value-satisfies-constraint value constraint (cons (cons index val) env))
        (value-satisfies-constraint value constraint env))))
)

(defthm choose-satisfying-value-property
  (implies
   (value-satisfies-constraint value constraint env)
   (value-satisfies-constraint (choose-satisfying-value constraint env) constraint env))
  :hints (("Goal" :use choose-satisfying-value)))

(defun-sk satisfying-value-exists (constraint env)
  (exists (value) (value-satisfies-constraint value constraint env)))

(defthm satisfying-value-exists-implies-successful-choice
  (implies
   (satisfying-value-exists constraint env)
   (value-satisfies-constraint (choose-satisfying-value constraint env) constraint env)))

(in-theory (disable satisfying-value-exists))

(def::un sample-constraint (c env)
  (declare (xargs :signature ((t t) rationalp)))
  (rfix (choose-satisfying-value c env)))

(defun sample-zoid (zoid)
  (if (not (consp zoid)) nil
    (let ((env (sample-zoid (cdr zoid))))
      (let ((constraint (car zoid)))
        (let ((v (sample-constraint constraint env)))
          (acons (var-index (constraint-var constraint)) v env))))))

(def::und restrict-constraint (constraint)
  (declare (xargs :signature ((t) t wf-zoid)))
  (mv constraint nil))

(skip-proofs
 (defthm restrict-constraint-indicies
   (>-all (var-index (constraint-var constraint))
          (zoid-indicies (val 1 (restrict-constraint constraint))))
   :rule-classes (:rewrite (:forward-chaining :trigger-terms ((zoid-indicies (val 1 (restrict-constraint constraint)))))))
 )

(skip-proofs
 (defthm restrict-constraint-property
   (implies
    (eval-zoid (val 1 (restrict-constraint constraint)) env)
    (satisfying-value-exists (val 0 (restrict-constraint constraint)) env)))
 )

(skip-proofs
 (defthm constraint-var-restrict-constraint
   (equal (constraint-var (val 0 (restrict-constraint x)))
          (constraint-var x)))
 )

(skip-proofs
 (defthm restricted-constraint-implies-constraint
   (implies
    (eval-constraint (val 0 (restrict-constraint constraint)) env)
    (eval-constraint constraint env))
   :rule-classes (:forward-chaining))
 )

(def::und intersect-zoid (x y) 
  (declare (xargs :signature ((wf-zoid wf-zoid) wf-zoid))
           (ignore y))
  x)

;; Technically this is too strong .. intersection is generalization.
(skip-proofs
 (defthm eval-intersect
   (equal (eval-zoid (intersect-zoid x y) env)
          (and (eval-zoid x env)
               (eval-zoid y env))))
 )

(skip-proofs
 (defun restrict-zoid (zoid)
   (if (not (consp zoid)) nil
     (let ((constraint (car zoid)))
       (met ((c2 res) (restrict-constraint constraint))
         (cons c2 (restrict-zoid (intersect-zoid (cdr zoid) res)))))))
 )

(skip-proofs
 (defthm >-all-intersect-zoid
   (equal (>-all key (zoid-indicies (intersect-zoid a b)))
          (and (>-all key (zoid-indicies a))
               (>-all key (zoid-indicies b))))))

(defthm >-all-restrict-zoid
  (implies
   (and
    (>-all key (zoid-indicies zoid))
    (wf-zoid zoid))
   (>-all key (zoid-indicies (restrict-zoid zoid)))))

(defthm wf-zoid-restrict-zoid
  (implies
   (wf-zoid zoid)
   (wf-zoid (restrict-zoid zoid))))

(defthm restricted-solution-satisfies-original-zoid
  (implies
   (and
    (eval-zoid (restrict-zoid zoid) env)
    (wf-zoid zoid))
   (eval-zoid zoid env))
  :rule-classes (:forward-chaining))

(defthm eval-zoid-intersect-zoid-implication
  (implies
   (eval-zoid (intersect-zoid a b) env)
   (and (eval-zoid a env)
        (eval-zoid b env)))
  :rule-classes (:forward-chaining))

(defthm sample-zoid-satisfies-zoid
  (implies
   (wf-zoid zoid)
   (eval-zoid (restrict-zoid zoid) (sample-zoid (restrict-zoid zoid))))
  :hints ((and stable-under-simplificationp
               '(:in-theory (enable eval-constraint)))))


