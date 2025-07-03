(*TODO: change theory name*)
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
"eval_term (Fun f args) vI fI = fI f (map (\<lambda>t. eval_term t vI fI) args)"

datatype ('v, 'f, 'p) formula =
Pred 'p "('v, 'f) fof_term list" |
And "('v, 'f, 'p) formula" "('v, 'f, 'p) formula" |
Or "('v, 'f, 'p) formula" "('v, 'f, 'p) formula" |
Not "('v, 'f, 'p) formula" |
Equal "('v, 'f, 'p) formula" "('v, 'f, 'p) formula" |
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
"eval_formula (Equal f1 f2) vI fI pI = ((eval_formula f1 vI fI pI) = (eval_formula f2 vI fI pI))" |
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

lemma not_not [simp]: "eval_formula (Not (Not f)) vI fI pI = eval_formula f vI fI pI"
  by auto

lemma and_de_morgan: "eval_formula (Not (And f1 f2)) vI fI pI = eval_formula (Or (Not f1) (Not f2)) vI fI pI"
  by auto

lemma or_de_morgan: "eval_formula (Not (Or f1 f2)) vI fI pI = eval_formula (And (Not f1) (Not f2)) vI fI pI"
  by auto

fun simp_formula :: "('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula" where
"simp_formula T = T" |
"simp_formula F = F" |
"simp_formula (Pred p args) = Pred p args" |
"simp_formula (And f1 f2) = (case (simp_formula f1, simp_formula f2) of
  (T, T) \<Rightarrow> T |
  (F, _) \<Rightarrow> F |
  (_, F) \<Rightarrow> F |
  (T, f2') \<Rightarrow> f2' |
  (f1', T) \<Rightarrow> f1' |
  (f1', f2') \<Rightarrow> And f1' f2'
)" |
"simp_formula (Or f1 f2) = (case (simp_formula f1, simp_formula f2) of
  (F, F) \<Rightarrow> F |
  (T, _) \<Rightarrow> T |
  (_, T) \<Rightarrow> T |
  (F, f2') \<Rightarrow> f2' |
  (f1', F) \<Rightarrow> f1' |
  (f1', f2') \<Rightarrow> Or f1' f2'
)" |
"simp_formula (Not f) = (case simp_formula f of
  T \<Rightarrow> F |
  F \<Rightarrow> T |
  f' \<Rightarrow> Not f'
)" |
"simp_formula (Equal f1 f2) = Equal (simp_formula f1) (simp_formula f2)" |
"simp_formula (Forall v f) = Forall v (simp_formula f)" |
"simp_formula (Exists v f) = Exists v (simp_formula f)"

end                                          