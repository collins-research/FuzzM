;; 
;; Copyright (C) 2017, Rockwell Collins
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;; 
;; 
(in-package "ACL2")

;; ---------------------------------------------------------

(defthm acl2-count-remove1
  (<= (acl2-count (remove1 x list))
      (acl2-count list))
  :rule-classes :linear)

(defthm member-acl2-count-remove1
  (implies
   (member x list)
   (< (acl2-count (remove1 x list))
      (acl2-count list)))
  :rule-classes (:forward-chaining :linear))

(defthm len-remove1
  (implies
   (member x list)
   (equal (len (remove1 x list))
          (1- (len list)))))

(defthm true-listp-remove1
  (implies
   (true-listp list)
   (true-listp (remove1 x list))))

(defthm nat-listp-remove1
  (implies
   (nat-listp list)
   (nat-listp (remove1 x list))))

;; ---------------------------------------------------------

(defthm not-member-remove
  (implies 
   (and 
    (not (member x list))
    (true-listp list))
   (equal (remove x list)
          list))
  :hints (("goal" :in-theory (enable remove))))

(defthm member-remove
  (iff (member x (remove y list))
       (and (not (equal x y))
            (member x list))))

(defthm acl2-number-listp-remove
  (implies
   (acl2-number-listp list)
   (acl2-number-listp (remove x list))))

;; ---------------------------------------------------------

(defun unique (list)
  "List contains no duplicates"
  (if (endp list) t
    (and (not (member (car list) (cdr list)))
         (unique (cdr list)))))

(defthm unique-remove
  (implies
   (unique list)
   (unique (remove x list))))

(defthm remove1-to-remove
  (implies
   (and
    (unique list)
    (true-listp list))
   (equal (remove1 x list)
          (remove x list)))
  :hints (("Goal" :in-theory (enable remove))))

(in-theory (disable remove))

;; ---------------------------------------------------------

(defun >-all (x list)
  "Recognizes when x is greater than all elements of list"
  (if (endp list) t
    (and (> x (car list))
         (>-all x (cdr list)))))

(defun >-ordered (list)
  "Identifies a strictly ordered (decreasing) list"
  (if (endp list) t
    (and (>-all (car list) (cdr list))
         (>-ordered (cdr list)))))

(encapsulate
    ()

  (local
   (defun >-all-alt (x list)
     (declare (xargs :measure (len list)))
     (if (endp list) t
       (and (> x (car list))
            (>-all-alt (1- x) (cdr list))))))

  (local
   (defthm peek
     (implies
      (and
       (not (>-all z list))
       (acl2-numberp x)
       (acl2-numberp z)
       (acl2-number-listp list)
       (<= x z))
      (not (>-all x list)))))

  (local
   (defun all-alt-induction (list z)
     (if (or (zp z) (endp list)) (list list z)
       (all-alt-induction (cdr list) (1- z)))))
  
  (local
   (defthm z-bound-helper
     (implies
      (and
       (natp z)
       (nat-listp list)
       (>-all-alt z list)
       (>-ordered list))
      (<= (len list) z))
     :hints (("goal" :induct (all-alt-induction list z)))))

  (local
   (defthm >-all-alt-def
     (implies
      (and
       (natp x)
       (nat-listp list)
       (>-ordered list))
      (iff (>-all-alt x list)
           (>-all x list)))
     :hints (("goal" :induct (>-all-alt x list)
              :do-not-induct t))))

  (defthm z-bound
    (implies
     (and
      (>-all z list)
      (natp z)
      (nat-listp list)
      (>-ordered list))
     (<= (len list) z))
    :rule-classes (:linear :forward-chaining))

  )

(defthm >-all-remove
  (implies
   (>-all z list)
   (>-all z (remove a list)))
  :hints (("Goal" :in-theory (enable remove))))

;; ---------------------------------------------------------

(defun get-largest-rec (x list)
  "Get element of list larger than x or x if it is always larger"
  (if (endp list) x
    (let ((entry (car list)))
      (if (< x entry) (get-largest-rec entry (cdr list))
        (get-largest-rec x (cdr list))))))

(defthm natp-get-largest-rec
  (implies
   (and
    (natp x)
    (nat-listp list))
   (natp (get-largest-rec x list)))
  :rule-classes (:type-prescription (:forward-chaining :trigger-terms ((get-largest-rec x list)))))

(defthm get-largest-rec-type
  (implies
   (and
    (acl2-numberp x)
    (acl2-number-listp list))
   (acl2-numberp (get-largest-rec x list)))
  :rule-classes (:type-prescription (:forward-chaining :trigger-terms ((get-largest-rec x list)))))

(defthm get-largest-rec-property
  (or (equal (get-largest-rec x list) x)
      (member (get-largest-rec x list) list))
  :rule-classes ((:forward-chaining :trigger-terms ((get-largest-rec x list)))))

(defthm get-largest-at-least-as-large
  (<= z (get-largest-rec z list))
  :rule-classes (:linear (:forward-chaining :trigger-terms ((get-largest-rec z list)))))

(defthm get-largest-rec-is-largest
  (implies
   (member x list)
   (<= x (get-largest-rec z list)))
  :rule-classes (:linear (:forward-chaining :trigger-terms ((get-largest-rec z list)))))

(defthm get-largest-arg-property
  (implies
   (not (equal (get-largest-rec z list) z))
   (< z (get-largest-rec z list)))
  :rule-classes (:linear (:forward-chaining :trigger-terms ((get-largest-rec z list)))))

(defthm get-largest-rec-is-the-largest-helper
  (implies 
   (and
    (acl2-numberp z)
    (equal (get-largest-rec z list) z))
   (>-all z (remove-equal z list)))
  :hints (("goal" :in-theory (enable remove))))

(defthm get-largest-rec-is-the-largest
  (implies
   (and
    (acl2-number-listp list)
    (acl2-numberp z)
    (unique list))
   (>-all (get-largest-rec z list) (remove-equal (get-largest-rec z list) list)))
  :hints (("Goal" :in-theory (enable remove))))

(defthm >-all-get-largest-rec
  (implies
   (and
    (>-all z list)
    (> z a))
   (< (get-largest-rec a list) z)))

;; ---------------------------------------------------------

(defun get-largest (list)
  "Get largest element of list or 0 is list is empty"
  (if (consp list) 
      (get-largest-rec (car list) (cdr list))
    0))

(defthm natp-get-largest
  (implies
   (nat-listp list)
   (natp (get-largest list)))
  :rule-classes (:type-prescription (:forward-chaining :trigger-terms ((get-largest list)))))

(defthm acl2-numberp-get-largest
  (implies
   (acl2-number-listp list)
   (acl2-numberp (get-largest list)))
  :rule-classes (:type-prescription (:forward-chaining :trigger-terms ((get-largest list)))))

(defthm member-get-largest
  (implies
   (consp list)
   (member (get-largest list) list))
  :rule-classes ((:forward-chaining :trigger-terms ((get-largest list)))))

(defthm get-largest-is-largest
  (implies
   (member x list)
   (<= x (get-largest list)))
  :rule-classes (:linear (:forward-chaining :trigger-terms ((member-equal x list)))))

(defthm get-largest-is-the-largest
  (implies
   (and
    (acl2-number-listp list)
    (consp list)
    (unique list))
   (>-all (get-largest list) (remove (get-largest list) list)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (remove) (not-member-remove)))))

(defthm >-all-get-largest
  (implies
   (and
    (>-all z list)
    (consp list))
   (< (get-largest list) z))
  :hints (("Goal" :in-theory (enable get-largest))))

(in-theory (disable get-largest))

;; ---------------------------------------------------------

(defun order (list)
  "Sort a list from largest to smallest"
  (if (endp list) nil
    (let ((x (get-largest list)))
      (cons x (order (remove1 x list))))))

(defthm nat-listp-order
  (implies
   (nat-listp list)
   (nat-listp (order list)))
  :rule-classes (:type-prescription (:forward-chaining :trigger-terms ((order list)))))

(defthm len-order
  (equal (len (order list))
         (len list))
  :hints (("Goal" :induct (order list))))

(defthm member-of-order
  (implies
   (and (true-listp list) (unique list))
   (iff (member x (order list))
        (member x list))))

(defthm order-preserves-uniqueness
  (implies
   (and
    (true-listp list)
    (unique list))
   (unique (order list))))

(defthm >-all-order
  (implies
   (and
    (unique list)
    (true-listp list)
    (>-all z list))
   (>-all z (order list))))

(defthm >-ordered-order
  (implies
   (and
    (acl2-number-listp list)
    (unique list))
   (>-ordered (order list))))

(in-theory (disable order))

;; ---------------------------------------------------------

(include-book "arithmetic-5/top" :dir :system)

(defun complete-sequence-p (list)
  "Recognizes a complete, strictly decreasing list of numbers"
  (if (endp list) t
    (and (equal (car list) (len (cdr list)))
         (complete-sequence-p (cdr list)))))

(defun sum (list)
  "Adds up all the numbers in a list"
  (if (endp list) 0
    (+ (car list)
       (sum (cdr list)))))

(defthm sum-remove1
  (equal (sum (remove1 x list))
         (if (member x list) (- (sum list) x)
           (sum list))))

(defthm sum-order
  (equal (sum (order list))
         (sum list))
  :hints (("Goal" :in-theory (enable order))))

;; ---------------------------------------------------------

(defun mk-sequence (n)
  "Constructs the list of numbers from N-1 to 0"
  (if (zp n) nil
    (let ((n (nfix n)))
      (cons (1- n) (mk-sequence (1- n))))))

(defthm len-mk-sequence
  (equal (len (mk-sequence n))
         (nfix n)))

(defthm mk-sequence-is-complete-sequence
  (complete-sequence-p (mk-sequence n)))

;; Just for fun ..
(defthmd sum-mk-sequence
  (equal (* 2 (sum (mk-sequence n)))
         (* (nfix n) (1- (nfix n)))))

;; ---------------------------------------------------------

(defthm complete-sequence-constitutes-a-lower-bound
  (implies
   (and
    (>-ordered list)
    (nat-listp list))
   (<= (sum (mk-sequence (len list))) (sum list)))
  :rule-classes (:forward-chaining :linear))

(defthmd ordered-sum-is-complete-sequence
  (implies
   (and
    (nat-listp list)
    (>-ordered list)
    (equal (sum (mk-sequence (len list))) (sum list)))
   (complete-sequence-p list)))

;; ---------------------------------------------------------

(defun complete-set-p (list)
  "The list contains 1 instance of every number from N-1 to 0"
  (if (not (consp list)) t
    (and (member (1- (len list)) list)
         (complete-set-p (remove1 (1- (len list)) list)))))

(defthm ordered-complete-sequence-p-implies-complete-set-p
  (implies
   (complete-sequence-p (order list))
   (complete-set-p list))
  :hints (("Goal" :in-theory (enable order))))

(defthm unique-sum-is-complete-set
  (implies
   (and
    (nat-listp list)
    (unique list)
    (equal (sum (mk-sequence (len list))) (sum list)))
   (complete-set-p list))
  :hints (("Goal" :do-not-induct t
           :use (:instance ordered-sum-is-complete-sequence
                           (list (order list))))))
