theory MU
  imports Main
begin

datatype Symbol = M | I | U

type_synonym word = "Symbol list"

inductive legit :: "word \<Rightarrow> bool" where
  start: "legit [M, I]"
| rule1: "\<lbrakk> legit (w @ [I]) \<rbrakk> \<Longrightarrow> legit (w @ [I, U])"
| rule2: "\<lbrakk> legit (M#x) \<rbrakk> \<Longrightarrow> legit ((M#x) @ x)"
| rule3: "\<lbrakk> legit (w @ [I,I,I] @ w') \<rbrakk> \<Longrightarrow> legit (w @ [U] @ w')"
| rule4: "\<lbrakk> legit (w @ [U,U] @ w') \<rbrakk> \<Longrightarrow> legit (w @ w')"

section \<open> Examples \<close>

lemma "legit [M,I,U] \<Longrightarrow> legit [M,I,U,I,U]"
  using rule2[of "[I,U]"] by simp

lemma "legit [M,U,M] \<Longrightarrow> legit [M,U,M,U,M]"
  using rule2[of "[U,M]"] by simp

lemma "legit [M,U] \<Longrightarrow> legit [M,U,U]"
  using rule2[of "[U]"] by simp

lemma "legit [U,M,I,I,I,M,U] \<Longrightarrow> legit [U,M,U,M,U]"
  using rule3[of "[U,M]" "[M,U]"] by simp

lemma "legit [M,I,I,I,I] \<Longrightarrow> legit [M,I,U]"
  using rule3[of "[M,I]" "[]"] by simp 

lemma "legit [M,I,I,I,I] \<Longrightarrow>  legit [M,U,I]"
  using rule3[of "[M]" "[I]"] by simp

lemma "legit [U,U,U] \<Longrightarrow> legit [U]"
  using rule4[of "[U]" "[]"] by simp

lemma "legit [M,U,U,U,I,I,I] \<Longrightarrow> legit [M,U,I,I,I]"
  using rule4[of "[M,U]" "[I,I,I]"] by simp

lemma "legit [M,U,I,I,U]"
proof -
  have "legit [M,I]"                by (simp add: start)
  then have "legit [M,I,I]"         using rule2[of "[I]"] by simp
  then have "legit [M,I,I,I,I]"     using rule2[of "[I,I]"] by simp
  then have "legit [M,I,I,I,I,U]"   using rule1[of "[M,I,I,I]"] by simp
  then have "legit [M,U,I,U]"       using rule3[of "[M]" "[I,U]"] by simp
  then have "legit [M,U,I,U,U,I,U]" using rule2[of "[U,I,U]"] by simp
  then have "legit [M,U,I,I,U]"     using rule4[of "[M,U,I]" "[I,U]"] by simp
  then show ?thesis .
qed

section \<open> Meta-Theorems \<close>

lemma legit_starts_with_M: "legit w \<Longrightarrow> hd w = M"
  apply(induction rule: legit.induct)
  apply(simp_all)
  apply (metis hd_append list.sel(1))  
  apply (metis Cons_eq_append_conv Symbol.distinct(2) hd_append2 list.sel(1))
  by (metis Symbol.distinct(4) append_eq_Cons_conv hd_append2 list.sel(1))

corollary "\<not> legit [U]"
  using legit_starts_with_M by force

fun number_of_I :: "word \<Rightarrow> nat" where
  "number_of_I [] = 0"
| "number_of_I (I#w) = 1 + number_of_I w"
| "number_of_I (_#w) = number_of_I w"

lemma number_of_I_append: "number_of_I (w @ v) = number_of_I w + number_of_I v"
  apply(induction w, simp_all)
  by (metis (full_types) Symbol.exhaust add_Suc number_of_I.simps(2) number_of_I.simps(3) number_of_I.simps(4) plus_1_eq_Suc)

lemma helper: "(n::nat) mod 3 \<noteq> 0 \<Longrightarrow> (2 * n) mod 3 \<noteq> 0"
proof(induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "(2 * (n + 1)) mod 3 = (((2 * n) mod 3) + 2) mod 3" using mod_Suc_Suc_eq by auto
  then show ?case
    by (metis Suc.prems Suc_1 Suc_eq_plus1 add.left_neutral eval_nat_numeral(3) mod_add_left_eq mod_mult_self2_is_0 mult.commute semiring_normalization_rules(2))
qed

lemma invariant: "legit w \<Longrightarrow> (number_of_I w) mod 3 \<noteq> 0"
proof(induction rule: legit.induct)
case start
  then show ?case by simp
next
  case (rule1 w)
  then show ?case by (simp add: number_of_I_append)
next
  case (rule2 x)
  have "number_of_I ((M # x) @ x) = 2 * number_of_I (M # x)" using number_of_I_append
    by simp
  then show ?case using helper rule2 by simp
next
  case (rule3 w w')
  have "number_of_I (w @ [I, I, I] @ w') = 3 + number_of_I w + number_of_I w'" by (simp add: number_of_I_append)
  then have "(number_of_I (w @ [I, I, I] @ w')) mod 3 = (number_of_I (w @ w')) mod 3"
    by (simp add: number_of_I_append)
  then show ?case using number_of_I_append rule3.IH by auto
next
  case (rule4 w w')
  then show ?case by (simp add: number_of_I_append)
qed

theorem "\<not> legit [M,U]"
proof -
  have "number_of_I [M,U] mod 3 = 0" by auto
  then show ?thesis
    using invariant by meson
qed

end