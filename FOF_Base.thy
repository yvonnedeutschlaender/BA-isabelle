theory FOF_Base
  imports Main
begin

datatype ('v, 'f) fof_term =
Var 'v |
Fun 'f "('v, 'f) fof_term list"

type_synonym ('v, 'd) I_var = "'v \<Rightarrow> 'd"
type_synonym ('f, 'd) I_fun = "'f \<Rightarrow> 'd list \<Rightarrow> 'd"

fun eval_term :: "('v, 'f) fof_term \<Rightarrow> ('v, 'd) I_var \<Rightarrow> ('f, 'd) I_fun \<Rightarrow> 'd" where
"eval_term (Var x) vI _ = vI x" |
"eval_term (Fun f args) vI fI = fI f (map (\<lambda>t. eval_term t vI fI) args)"

datatype ('v, 'f, 'p) formula =
Pred 'p "('v, 'f) fof_term list" |
And "('v, 'f, 'p) formula" "('v, 'f, 'p) formula" |
Or "('v, 'f, 'p) formula" "('v, 'f, 'p) formula" |
Not "('v, 'f, 'p) formula" |
Equal "('v, 'f) fof_term" "('v, 'f) fof_term" |
Forall 'v "('v, 'f, 'p) formula" |
Exists 'v "('v, 'f, 'p) formula" |
T | 
F

type_synonym ('p, 'd) I_pred = "'p \<Rightarrow> 'd list \<Rightarrow> bool"

fun eval_formula ::
"('v, 'f, 'p) formula \<Rightarrow> ('v, 'd) I_var \<Rightarrow> ('f, 'd) I_fun \<Rightarrow> ('p, 'd) I_pred \<Rightarrow> bool" where
"eval_formula (Pred p args) vI fI pI = pI p (map (\<lambda>t. eval_term t vI fI) args) " |
"eval_formula (And f1 f2) vI fI pI = ((eval_formula f1 vI fI pI) \<and> (eval_formula f2 vI fI pI))" |
"eval_formula (Or f1 f2) vI fI pI = ((eval_formula f1 vI fI pI) \<or> (eval_formula f2 vI fI pI))" |
"eval_formula (Not f) vI fI pI = (\<not>(eval_formula f vI fI pI))" |
"eval_formula (Equal t1 t2) vI fI pI = ((eval_term t1 vI fI) = (eval_term t2 vI fI))" |
"eval_formula (Forall v f) vI fI pI = (\<forall>x. eval_formula f (vI(v := x)) fI pI)" |
"eval_formula (Exists v f) vI fI pI = (\<exists>x. eval_formula f (vI(v := x)) fI pI)" |
"eval_formula T _ _ _ = True" |
"eval_formula F _ _ _ = False"

definition Imp :: "('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula" where
"Imp f1 f2 = Or (Not f1) f2"

definition Equiv :: "('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula" where
"Equiv f1 f2 = And (Imp f1 f2) (Imp f2 f1)"

definition Xor :: "('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula" where
"Xor f1 f2 = Or (And (Not f1) f2) (And f1 (Not f2))"

(*TODO: erweitern *)
lemma excluded_middle: "eval_formula (Or f (Not f)) vI fI pI"
  by auto

lemma and_de_morgan: "eval_formula (Not (And f1 f2)) vI fI pI = eval_formula (Or (Not f1) (Not f2)) vI fI pI"
  by auto

lemma or_de_morgan: "eval_formula (Not (Or f1 f2)) vI fI pI = eval_formula (And (Not f1) (Not f2)) vI fI pI"
  by auto

end                                          