(in-package "ACL2")
(include-book "coi/util/defun" :dir :system)

;;
;; This seems like a reasonable approach to variable allocation.
;;

(defun weak-prat-p (x)
  (declare (type t x))
  (and (rationalp x)
       (<= 0 x)))

(defthm weak-prat-implication
  (implies
   (weak-prat-p x)
   (and (rationalp x)
        (<= 0 x)))
  :rule-classes (:forward-chaining))

(defun prat-p (x)
  (declare (type t x))
  (and (rationalp x)
       (< 0 x)))

(defun prat-listp (x)
  (declare (type t x))
  (if (not (consp x)) t
    (and (prat-p (car x))
         (prat-listp (cdr x)))))

(defthm prat-p-implies-weak-prat-p
  (implies
   (prat-p x)
   (and (weak-prat-p x)
        (< 0 x)))
  :rule-classes :forward-chaining)

(def::und prat-fix (x)
  (declare (xargs :signature ((t) weak-prat-p)))
  (if (prat-p x) x 0))

(defthm prat-fix-id
  (implies
   (weak-prat-p x)
   (equal (prat-fix x) x))
  :hints (("Goal" :in-theory (enable prat-fix))))

(defun >-all (x list)
  (declare (type t list))
  (if (not (consp list)) t
    (and (> (prat-fix x) (prat-fix (car list)))
         (>-all x (cdr list)))))

(defthm >-all-chaining
  (implies
   (and
    (>-all x list)
    (>= (prat-fix y) (prat-fix x)))
   (>-all y list))
  :rule-classes (:rewrite))

(defun >-ordered-p (list)
  (declare (type t list))
  (if (not (consp list)) t
    (and (>-all (car list) (cdr list))
         (>-ordered-p (cdr list)))))

(def::und alloc-between (a b)
  (declare (xargs :signature ((weak-prat-p prat-p) prat-p)))
  (/ (+ (prat-fix a) (prat-fix b)) 2))

(defthm mid-point-theorem
  (implies
   (and
    (weak-prat-p a)
    (prat-p b)
    (< a b))
   (and (< a (alloc-between a b))
        (< (alloc-between a b) b)))
  :hints (("Goal" :in-theory (enable prat-fix alloc-between)))
  :rule-classes ((:forward-chaining :trigger-terms ((alloc-between a b)))
                 :linear))

;; Make the list decrease ..

(in-theory (disable prat-p weak-prat-p))

(defun >-prat-listp (x)
  (declare (type t x))
  (and (prat-listp x)
       (>-ordered-p x)))

(defthm implies->-prat-listp
  (implies
   (and (>-ordered-p x)
        (prat-listp x))
   (>-prat-listp x))
  :rule-classes (:forward-chaining :rewrite :type-prescription))

(defthm >-prat-listp-implies
  (implies
   (>-prat-listp x)
   (and (>-ordered-p x)
        (prat-listp x)))
  :rule-classes (:forward-chaining))

(defthm consp->-prat-listp
  (implies
   (and
    (>-prat-listp x)
    (consp x))
   (and (prat-p (car x))
        (>-all (car x) (cdr x))))
  :rule-classes (:forward-chaining))

(defthm open->-prat-listp
  (implies
   (consp x)
   (equal (>-prat-listp x)
          (and (prat-p (car x))
               (>-all (car x) (cdr x))
               (>-prat-listp (cdr x)))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(in-theory (disable >-prat-listp))

(def::un alloc-after (x list)
  (declare (xargs :signature ((prat-p >-prat-listp) prat-p)))
  (if (not (consp list)) (alloc-between 0 x)
    (if (> (prat-fix x) (prat-fix (car list))) (alloc-between (prat-fix (car list)) (prat-fix x))
      (alloc-after x (cdr list)))))

(def::un after (x list)
  (declare (xargs :signature ((prat-p >-prat-listp) weak-prat-p)))
  (if (not (consp list)) 0
    (if (> (prat-fix x) (prat-fix (car list))) (prat-fix (car list))
      (after x (cdr list)))))

(defthm exclusive-bounds
  (implies
   (and
    (prat-p x)
    (prat-p a)
    (>-prat-listp list)
    (< a x)
    (< (after x list) a))
   (not (member a list))))

(defthm alloc-after-upper-bound
  (implies
   (prat-p x)
   (< (alloc-after x list) x))
  :rule-classes (:linear (:forward-chaining :trigger-terms ((alloc-after x list)))))
  
(defthm alloc-after-lower-bound
  (implies
   (and
    (prat-p x)
    (>-prat-listp list))
   (< (after x list) (alloc-after x list)))
  :rule-classes (:linear (:forward-chaining :trigger-terms ((alloc-after x list)))))

;; Essentially: where does x appear in the list?
(def::un order (x list)
  (declare (xargs :signature ((t t) natp)))
  (if (not (consp list)) 0
    (if (equal (prat-fix x) (prat-fix (car list))) (len list)
      (order x (cdr list)))))

(defthm member-implies-non-zero-order
  (implies
   (member x list)
   (< 0 (order x list)))
  :rule-classes (:linear :forward-chaining))

(defthm not-member-implies-zero-order
  (implies
   (and
    (not (member x list))
    (prat-p x)
    (prat-listp list))
   (equal (order x list) 0)))

(defthm order-invariant
  (implies
   (and
    (member x list)
    (member y list)
    (prat-p x)
    (prat-p y)
    (>-prat-listp list))
   (iff (< (order x list) (order y list))
        (< x y))))

;;
;;
;;

(def::un >-insert (x list)
  (declare (xargs :signature ((prat-p prat-listp) prat-listp)))
  (if (not (consp list)) (list x)
    (let ((entry (prat-fix (car list))))
      (if (= (prat-fix x) entry) list
        (if (> (prat-fix x) entry) (cons (prat-fix x) list)
          (cons (car list) (>-insert x (cdr list))))))))

(defthm >-all-insert
  (iff (>-all x (>-insert b list))
       (and (> (prat-fix x) (prat-fix b))
            (>-all x list))))

(defthm ordered-insert
  (implies
   (>-ordered-p list)
   (>-ordered-p (>-insert x list))))

(def::signature >-insert (prat-p >-prat-listp) >-prat-listp)

(defthm insert-is-conservative
  (implies
   (and
    (prat-listp list)
    (member x list))
   (member x (>-insert a list))))

(defthm after-alloc-after
  (implies
   (and
    (prat-p x)
    (>-prat-listp list))
   (equal (after x (>-insert (alloc-after x list) list))
          (alloc-after x list))))

