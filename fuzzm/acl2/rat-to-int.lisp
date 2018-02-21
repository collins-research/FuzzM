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

;; This file dictates the kinds of transformations that
;; we can perform on rational poly's of integer variables.

;; ============ (< x q) ================

(defun z< (q)
  (if (integerp q) (1- q)
    (floor q 1)))

(defun r< (q)
  (- q (z< q)))

(defthm integerp-z<
  (implies
   (rationalp q)
   (integerp (z< q))))

(defthm rationalp-r<
  (implies
   (rationalp q)
   (rationalp (r< q))))

(defthm r<-bounds
  (implies
   (rationalp q)
   (and (< 0 (r< q))
        (<= (r< q) 1)))
  :rule-classes nil)

(defthm rational-z<-r<-decomposition
  (implies
   (rationalp q)
   (equal q (+ (z< q) (r< q))))
  :rule-classes nil)

(defthm lt-to-leq-z<
  (implies
   (and
    (integerp x)
    (rationalp q))
   (iff (< x q)
        (<= x (z< q))))
  :rule-classes nil)

;; ============ (<= x q) ================

(defun z<= (q)
  (floor q 1))

(defun r<= (q)
  (- q (z<= q)))

(defthm integerp-z<=
  (implies
   (rationalp q)
   (integerp (z<= q))))

(defthm rationalp-r<=
  (implies
   (rationalp q)
   (rationalp (r<= q))))

(defthm r<=-bounds
  (implies
   (rationalp q)
   (and (<= 0 (r<= q))
        (< (r<= q) 1)))
  :rule-classes nil)

(defthm rational-z<=-r<=-decomposition
  (implies
   (rationalp q)
   (equal q (+ (z<= q) (r<= q))))
  :rule-classes nil)

(defthm leq-to-leq-z<=
  (implies
   (and
    (integerp x)
    (rationalp q))
   (iff (<= x q)
        (<= x (z<= q))))
  :rule-classes nil)

;; ============ (< q x) ================

(defun z> (q)
  (- (z< (- q))))

(defun r> (q)
  (- q (z> q)))

(defthm integerp-z>
  (implies
   (rationalp q)
   (integerp (z> q))))

(defthm rationalp-r>
  (implies
   (rationalp q)
   (rationalp (r> q))))

(defthm r>-bounds
  (implies
   (rationalp q)
   (and (< (r> q) 0)
        (<= -1 (r> q))))
  :rule-classes nil)

(defthm rational-z>-r>-decomposition
  (implies
   (rationalp q)
   (equal q (+ (z> q) (r> q))))
  :rule-classes nil)

(defthm lt-to-leq-z>
  (implies
   (and
    (integerp x)
    (rationalp q))
   (iff (< q x)
        (<= (z> q) x)))
  :rule-classes nil)

;; ============ (<= q x) ================

(defun z>= (q)
  (- (z<= (- q))))

(defun r>= (q)
  (- q (z>= q)))

(defthm integerp-z>=
  (implies
   (rationalp q)
   (integerp (z>= q))))

(defthm rationalp-r>=
  (implies
   (rationalp q)
   (rationalp (r>= q))))

(defthm r>=-bounds
  (implies
   (rationalp q)
   (and (<= (r>= q) 0)
        (< -1 (r>= q))))
  :rule-classes nil)

(defthm rational-z>=-r>=-decomposition
  (implies
   (rationalp q)
   (equal q (+ (z>= q) (r>= q))))
  :rule-classes nil)

(defthm leq-to-leq-z>=
  (implies
   (and
    (integerp x)
    (rationalp q))
   (iff (<= q x)
        (<= (z>= q) x)))
  :rule-classes nil)

