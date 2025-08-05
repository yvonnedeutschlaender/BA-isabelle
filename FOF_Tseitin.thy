theory FOF_Tseitin
  imports Main FOF_Base
begin

inductive is_prop :: "('v, 'f, 'p) formula \<Rightarrow> bool" where
True: "is_prop T" |
False: "is_prop F" |
Prop: "is_prop (Pred P [])" |
And: "is_prop f1 \<Longrightarrow> is_prop f2 \<Longrightarrow> is_prop (And f1 f2)" |
Or: "is_prop f1 \<Longrightarrow> is_prop f2 \<Longrightarrow> is_prop (Or f1 f2)" |
Not: "is_prop f \<Longrightarrow> is_prop (Not f)"

inductive is_literal :: "('v, 'f, 'p) formula \<Rightarrow> bool" where
True: "is_literal T" |
False: "is_literal F" |
Pred: "is_literal (Pred p args)" |
Equal: "is_literal (Equal t1 t2)" |
NTrue: "is_literal (Not T)" |
NFalse: "is_literal (Not F)" |
NPred: "is_literal (Not (Pred p args))" |
NEqual: "is_literal (Not (Equal t1 t2))"

inductive is_nnf :: "('v, 'f, 'p) formula \<Rightarrow> bool" where
Literal: "is_literal f \<Longrightarrow> is_nnf f" |
And: "is_nnf f1 \<Longrightarrow> is_nnf f2 \<Longrightarrow> is_nnf (And f1 f2)" |
Or: "is_nnf f1 \<Longrightarrow> is_nnf f2 \<Longrightarrow> is_nnf (Or f1 f2)" |
Forall: "is_nnf f \<Longrightarrow> is_nnf (Forall v f)" |
Exists: "is_nnf f \<Longrightarrow> is_nnf (Exists v f)"

(*
inductive is_clausel :: "('v, 'f, 'p) formula \<Rightarrow> bool" where
Literal: "is_literal f \<Longrightarrow> is_clausel f" |
Or: "is_literal f1 \<Longrightarrow> is_literal f2 \<Longrightarrow> is_clausel (Or f1 f2)"

inductive is_cnf :: "('v, 'f, 'p) formula \<Rightarrow> bool" where
Literal: "is_literal f \<Longrightarrow> is_cnf f" |
And: "is_clausel f1 \<Longrightarrow> is_clausel f2 \<Longrightarrow> is_cnf (And f1 f2)" 
*)

type_synonym 'p fresh = "'p set \<Rightarrow> 'p"
type_synonym ('v, 'f, 'p) tseitin_assign = "(('v, 'f, 'p) formula \<times> ('v, 'f, 'p) formula)"

fun tseitin_occup_var :: "('v, 'f, 'p) formula \<Rightarrow> 'p set" where
"tseitin_occup_var (Pred p []) = {p}" |
"tseitin_occup_var (Not (Pred p [])) = {p}" |
"tseitin_occup_var (And f1 f2) = tseitin_occup_var f1 \<union> tseitin_occup_var f2" |
"tseitin_occup_var (Or f1 f2) = tseitin_occup_var f1 \<union> tseitin_occup_var f2" |
"tseitin_occup_var _ = {}"

definition tseitin_fresh_var :: "'p fresh \<Rightarrow> 'p set \<Rightarrow> 'p set \<times> 'p" where
"tseitin_fresh_var \<xi> \<Sigma> = (let \<tau> = \<xi> \<Sigma> in (\<Sigma> \<union> {\<tau>}, \<tau>))"

definition tseitin_assign_var :: "'p \<Rightarrow> ('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) tseitin_assign" where
"tseitin_assign_var \<tau> f = (Pred \<tau> [], f)"

fun tseitin_subst_formula :: 
  "('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) tseitin_assign list  \<Rightarrow> ('v, 'f, 'p) formula" where
"tseitin_subst_formula f [] = f" |
"tseitin_subst_formula f (a # as) = (if f = (snd a) then (fst a) else tseitin_subst_formula f as)"

fun tseitin_list ::
  "'p fresh \<Rightarrow> 'p set \<Rightarrow> ('v, 'f, 'p) formula \<Rightarrow> 'p set \<times> ('v, 'f, 'p) tseitin_assign list" where
"tseitin_list \<xi> \<Sigma> T = 
  (let \<tau> = tseitin_fresh_var \<xi> \<Sigma> 
    in (fst \<tau>, [tseitin_assign_var (snd \<tau>) T]) )" |
"tseitin_list \<xi> \<Sigma> F = 
  (let \<tau> = tseitin_fresh_var \<xi> \<Sigma> 
    in (fst \<tau>, [tseitin_assign_var (snd \<tau>) F]) )" |
"tseitin_list \<xi> \<Sigma> (Pred p []) = 
  (let \<tau> = tseitin_fresh_var \<xi> \<Sigma> 
    in (fst \<tau>, [tseitin_assign_var (snd \<tau>) (Pred p []) ]) )" |
"tseitin_list \<xi> \<Sigma> (Not (Pred p [])) = 
  (let \<tau> = tseitin_fresh_var \<xi> \<Sigma> 
    in (fst \<tau>, [tseitin_assign_var (snd \<tau>) (Not (Pred p [])) ]) )" |
"tseitin_list \<xi> \<Sigma> (And f1 f2) = 
  (let \<tau> = tseitin_fresh_var \<xi> \<Sigma>;
       f1_list = tseitin_list \<xi> (fst \<tau>) f1;
       f2_list = tseitin_list \<xi> (fst f1_list) f2;
       f1_subst = tseitin_subst_formula f1 (snd f1_list);
       f2_subst = tseitin_subst_formula f2 (snd f2_list)
   in (fst f2_list, 
      [tseitin_assign_var (snd \<tau>) (And f1_subst f2_subst)] @ (snd f1_list) @ (snd f2_list)) )" |
"tseitin_list \<xi> \<Sigma> (Or f1 f2) = 
  (let \<tau> = tseitin_fresh_var \<xi> \<Sigma>;
       f1_list = tseitin_list \<xi> (fst \<tau>) f1;
       f2_list = tseitin_list \<xi> (fst f1_list) f2;
       f1_subst = tseitin_subst_formula f1 (snd f1_list);
       f2_subst = tseitin_subst_formula f2 (snd f2_list)
   in (fst f2_list, 
      [tseitin_assign_var (snd \<tau>) (Or f1_subst f2_subst)] @ (snd f1_list) @ (snd f2_list)) )" |
"tseitin_list _ \<Sigma> _ = (\<Sigma>, [])"


(*Testing:
value "tseitin_list fresh (tseitin_occup_var T) T"
value "tseitin_list fresh (tseitin_occup_var (Pred ''a'' []))  (Pred ''a'' [])"
value "tseitin_list fresh (tseitin_occup_var (And (Pred ''a'' []) (Pred ''b'' []))) (And (Pred ''a'' []) (Pred ''b'' []))"
value "tseitin_list fresh (tseitin_occup_var (And (And T (Pred ''a'' [])) F)) (And (And T (Pred ''a'' [])) F)"
value "tseitin_occup_var (Not (And (Pred p []) (Pred a [])))"
value "tseitin_occup_var (And (Pred ''p'' []) (Or (Pred ''g'' []) (Not (Pred ''u'' []))))"
value "tseitin_assigned_var [(Pred ''a'' [], T), (Pred ''g'' [], F)]"
*)


fun tseitin_assignm_to_cnf :: "('v, 'f, 'p) tseitin_assign \<Rightarrow> ('v, 'f, 'p) formula" where
"tseitin_assignm_to_cnf (\<tau>, \<phi>) =
  (let l = Imp \<tau> \<phi>;
       r = Imp \<phi> \<tau>
    in case \<phi> of
        And \<phi>1 \<phi>2 \<Rightarrow> And (distribute_formula l) (demorg_formula r) |
        Or \<phi>1 \<phi>2 \<Rightarrow> And l (distribute_formula (demorg_formula r)) |
        _ \<Rightarrow> And l r
)"

fun tseitin_list_to_cnf :: "('v, 'f, 'p) tseitin_assign list \<Rightarrow> ('v, 'f, 'p) formula" where
"tseitin_list_to_cnf [] = T" |
"tseitin_list_to_cnf (a # as) = And (tseitin_assignm_to_cnf a) (tseitin_list_to_cnf as)"

(*TODO: \<phi> to NNF*)
fun tseitin_expansion :: "'p fresh \<Rightarrow> ('v, 'f, 'p) formula \<Rightarrow> ('v, 'f, 'p) formula" where
"tseitin_expansion \<xi> \<phi> = 
  (let list = snd (tseitin_list \<xi> (tseitin_occup_var \<phi>) \<phi>)
    in And (tseitin_subst_formula \<phi> list) (tseitin_list_to_cnf list))"

(*TODO:
theorem
  fixes fresh :: "'p set \<Rightarrow> 'p" and \<phi> :: "('v, 'f, 'p) formula"
  assumes "\<And>\<P>. finite \<P> \<Longrightarrow> fresh \<P> \<notin> \<P>"
  assumes "is_nnf \<phi>"
  assumes "is_prop \<phi>"
  shows "(\<exists>pI. eval_formula (tseitin_expansion fresh \<phi>) vI fI pI) \<longleftrightarrow> (\<exists>pI. eval_formula \<phi> vI fI pI)"
 sorry
*)

end