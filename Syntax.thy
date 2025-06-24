theory Syntax
  imports Main
begin

datatype ('v, 'f) fof_term =
Var 'v |
Fun 'f "('v, 'f) fof_term list"

type_synonym ('v, 'd) I_var = "'v \<Rightarrow> 'd"
type_synonym ('f, 'd) I_fun = "'f \<Rightarrow> 'd list \<Rightarrow> 'd"

fun eval_term :: "('v, 'f) fof_term \<Rightarrow> ('v, 'd) I_var \<Rightarrow> ('f, 'd) I_fun \<Rightarrow> 'd" where
"eval_term (Var x) vI _ = vI x" |
"eval_term (Fun f []) _ fI = fI f []" |
"eval_term (Fun f args) vI fI = fI f (map (\<lambda>t. eval_term t vI fI) args)"



datatype ('v, 'f, 'p) formula =
Pred 'p "('v, 'f) fof_term list" |
And "('v, 'f, 'p) formula" "('v, 'f, 'p) formula" |
Or "('v, 'f, 'p) formula" "('v, 'f, 'p) formula" |
Not "('v, 'f, 'p) formula"
(*TODO:
Equal
Forall
Exists
 *)

type_synonym ('p, 'd) I_pred = "'p \<Rightarrow> 'd list \<Rightarrow> bool"

fun eval_formula ::
"('v, 'f, 'p) formula \<Rightarrow> ('v, 'd) I_var \<Rightarrow> ('f, 'd) I_fun \<Rightarrow> ('p, 'd) I_pred \<Rightarrow> bool" where
"eval_formula (Pred p args) vI fI pI = pI p (map (\<lambda>t. eval_term t vI fI) args) " |
"eval_formula (And f1 f2) vI fI pI = ((eval_formula f1 vI fI pI) \<and> (eval_formula f2 vI fI pI))" |
"eval_formula (Or f1 f2) vI fI pI = ((eval_formula f1 vI fI pI) \<or> (eval_formula f2 vI fI pI))" |
"eval_formula (Not f) vI fI pI = (\<not>(eval_formula f vI fI pI))"

definition imp :: "('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula" where
"imp f1 f2 = Or (Not f1) f2"

definition equiv :: "('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula" where
"equiv f1 f2 = And (imp f1 f2) (imp f2 f1)"

definition xor :: "('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula" where
"xor f1 f2 = Or (And (Not f1) f2) (And f1 (Not f2))"

(*TODO: erweitern *)
lemma excluded_middle : "eval_formula (Or f (Not f)) vI fI pI"
  by auto

lemma not_not [simp] : "eval_formula (Not (Not f)) vI fI pI = eval_formula f vI fI pI"
  by auto

lemma and_de_morgan: "eval_formula (Not (And f1 f2)) vI fI pI = eval_formula (Or (Not f1) (Not f2)) vI fI pI"
  by auto

lemma or_de_morgan : "eval_formula (Not (Or f1 f2)) vI fI pI = eval_formula (And (Not f1) (Not f2)) vI fI pI"
  by auto

end                                          