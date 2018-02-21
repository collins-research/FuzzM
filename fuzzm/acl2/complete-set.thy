(*******************************************************************)
(* Copyright (C) 2017, Rockwell Collins                            *)
(* All rights reserved.                                            *)
(*                                                                 *)
(* This software may be modified and distributed under the terms   *)
(* of the 3-clause BSD license.  See the LICENSE file for details. *)
(*******************************************************************)

theory CompleteSet
imports Main Finite_Set
begin


-- {* Define {\it suitable} which deconstructs a set by always taking out its largest element *}

inductive suitable :: "nat set \<Rightarrow> bool"
  where
    oneI [simp]: "x > 0 \<Longrightarrow> suitable {x}"
  | insertI [simp]: "\<lbrakk> suitable S; Max S < x \<rbrakk> \<Longrightarrow> suitable (insert x S)"

lemma max_less_notin[simp]:
  "\<lbrakk> finite S; S \<noteq> {}; Max S < x \<rbrakk> \<Longrightarrow> x \<notin> S"
by auto

declare Max_less_iff[simp del] Max_le_iff[simp del]

lemma suitable_finite[simp]:
  "suitable S \<Longrightarrow> finite S"
by (induction rule: suitable.induct, auto)

lemma suitable_nonempty[simp]:
  "suitable S \<Longrightarrow> S \<noteq> {}"
by (induction rule: suitable.induct, auto)


-- {* Prove our property for {\it suitable} sets *}

lemma max_ge_card[dest]:
  "suitable S \<Longrightarrow> card S \<le> Max S"
by (induction rule: suitable.induct, auto)

lemma suitable_lower_bound[dest]:
  "suitable S \<Longrightarrow> card S * (card S + 1) \<le> 2 * Sum S"
by (induction rule: suitable.induct, auto)

lemma suitable_exact_n: (* This doesn't require induction, just case analysis *)
  "\<lbrakk> suitable S; 2 * Sum S = card S * (card S + 1) \<rbrakk> \<Longrightarrow> card S \<in> S"
apply (induction rule: suitable.induct, simp)
apply (subgoal_tac "1 + card S \<ge> x", auto)
done

lemma suitable_exact_set:
  "\<lbrakk> suitable S; 2 * Sum S = card S * (card S + 1) \<rbrakk> \<Longrightarrow> S = {Suc 0..card S}"
apply (induction rule: suitable.induct, simp)
apply (subgoal_tac "x = card S + 1")
apply (simp add: atLeastAtMostSuc_conv)
apply (subgoal_tac "x > card S")
apply auto
done


-- {* Prove a declarative description of {\it suitable} sets *}

lemma suitable_insert:
  "\<lbrakk> suitable S; x > 0 \<rbrakk> \<Longrightarrow> suitable (insert x S)"
apply (induction rule: suitable.induct)
apply (metis Max_singleton insert_absorb2 insert_commute linorder_cases suitable.simps)
apply (case_tac "xa > x")
apply (subst insert_commute)
apply simp
apply (case_tac "xa = x")
apply simp
apply simp
done

lemma suitable_declarative:
  "\<lbrakk> finite S; S \<noteq> {}; \<forall>x\<in>S. 0 < x \<rbrakk> \<Longrightarrow> suitable S"
apply (induction rule: finite_induct, simp)
apply (metis insert_iff oneI suitable_insert)
done


-- {* Put it all together *}

theorem main_result:
  "\<lbrakk> finite S; S \<noteq> {}; \<forall>x\<in>S. 0 < x;
     2 * Sum S = card S * (card S + 1) \<rbrakk> \<Longrightarrow> S = {1..card S}"
by (simp add: suitable_declarative suitable_exact_set)

end