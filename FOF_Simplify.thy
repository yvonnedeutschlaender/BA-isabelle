theory FOF_Simplify
  imports Main FOF_Base
begin

lemma eval_formula_Not_Not: "eval_formula (Not (Not f)) vI fI pI = eval_formula f vI fI pI"
  by simp

lemma eval_formula_simp_formula_Not_equiv:
  assumes IH: "eval_formula (simp_formula \<phi>) vI fI pI = eval_formula \<phi> vI fI pI"
  shows "eval_formula (simp_formula (Not \<phi>)) vI fI pI = eval_formula (Not \<phi>) vI fI pI"
proof (cases "simp_formula \<phi>")
  case (Pred p args)
  have "eval_formula (simp_formula (Not \<phi>)) vI fI pI = eval_formula (Not (Pred p args)) vI fI pI"
    using simp_formula.simps `simp_formula \<phi> = (Pred p args)`
    by simp
  also have "... = (\<not>(eval_formula (Pred p args) vI fI pI))"
    using eval_formula.simps
    by simp
  also have "... = (\<not>(eval_formula \<phi>) vI fI pI)"
    using `simp_formula \<phi> = (Pred p args)` IH
    by simp
  also have "... = eval_formula (Not \<phi>) vI fI pI"
    using eval_formula.simps
    by simp
  finally show ?thesis .
next
  case (And f1 f2)
  have "eval_formula (simp_formula (Not \<phi>)) vI fI pI = eval_formula (Not (And f1 f2)) vI fI pI"
    using simp_formula.simps `simp_formula \<phi> = (And f1 f2)` 
    by simp
  also have "... = (\<not>(eval_formula (And f1 f2) vI fI pI))"
    using eval_formula.simps
    by simp
  also have "... = eval_formula (Not \<phi>) vI fI pI"
    using `simp_formula \<phi> = (And f1 f2)` IH eval_formula.simps
    by simp
  finally show ?thesis .
next
  case (Or f1 f2)
  have "eval_formula (simp_formula (Not \<phi>)) vI fI pI = eval_formula (Not (Or f1 f2)) vI fI pI"
    using simp_formula.simps `simp_formula \<phi> = (Or f1 f2)` 
    by simp
  also have "... = (\<not>(eval_formula (Or f1 f2) vI fI pI))"
    using eval_formula.simps
    by simp
  also have "... = eval_formula (Not \<phi>) vI fI pI"
    using `simp_formula \<phi> = (Or f1 f2)` IH eval_formula.simps
    by simp
  finally show ?thesis .  
next
  case (Not f)
  have "eval_formula (simp_formula (Not \<phi>)) vI fI pI = eval_formula f vI fI pI"
    using simp_formula.simps `simp_formula \<phi> = (Not f)` eval_formula_Not_Not
    by simp
  also have "... = (\<not>(\<not>(eval_formula f vI fI pI)))"
    using eval_formula_Not_Not
    by simp
  also have "... = (\<not>(eval_formula \<phi> vI fI pI))"
    using eval_formula.simps `simp_formula \<phi> = (Not f)` IH
    by simp
  also have "... = eval_formula (Not \<phi>) vI fI pI"
    using eval_formula.simps
    by simp 
  finally show ?thesis .
next
  case (Equal t1 t2)
  have "eval_formula (simp_formula (Not \<phi>)) vI fI pI = eval_formula (Not (Equal t1 t2)) vI fI pI"
    using simp_formula.simps `simp_formula \<phi> = (Equal t1 t2)`
    by simp
  also have "... = (\<not>(eval_formula (Equal t1 t2) vI fI pI))"
    using eval_formula.simps
    by simp
  also have "... = eval_formula (Not \<phi>) vI fI pI"
    using `simp_formula \<phi> = (Equal t1 t2)` IH eval_formula.simps
    by simp
  finally show ?thesis .
next
  case (Forall v f)
  have "eval_formula (simp_formula (Not \<phi>)) vI fI pI = eval_formula (Not (Forall v f)) vI fI pI"
    using simp_formula.simps `simp_formula \<phi> = (Forall v f)`
    by simp
  also have "... = (\<not>(eval_formula (Forall v f) vI fI pI))"
    using eval_formula.simps
    by simp
  also have "... = eval_formula (Not \<phi>) vI fI pI"
    using `simp_formula \<phi> = (Forall v f)` IH eval_formula.simps
    by simp
  finally show ?thesis .
next
  case (Exists v f)
  have "eval_formula (simp_formula (Not \<phi>)) vI fI pI = eval_formula (Not (Exists v f)) vI fI pI"
    using simp_formula.simps `simp_formula \<phi> = (Exists v f)`
    by simp
  also have "... = (\<not>(eval_formula (Exists v f) vI fI pI))"
    using eval_formula.simps
    by simp
  also have "... = eval_formula (Not \<phi>) vI fI pI"
    using `simp_formula \<phi> = (Exists v f)` IH eval_formula.simps
    by simp
  finally show ?thesis .
next
  case T
  have "eval_formula (simp_formula (Not \<phi>)) vI fI pI = False"
    using simp_formula.simps `simp_formula \<phi> = T` eval_formula.simps
    by simp
  also have "... = (\<not>(eval_formula T vI fI pI))"
    using eval_formula.simps
    by simp
  also have "... = eval_formula (Not \<phi>) vI fI pI"
    using `simp_formula \<phi> = T` IH eval_formula.simps
    by simp
  finally show ?thesis .
next
  case F
  have "eval_formula (simp_formula (Not \<phi>)) vI fI pI = True"
    using simp_formula.simps `simp_formula \<phi> = F` eval_formula.simps
    by simp
  also have "... = (\<not>(eval_formula F vI fI pI))"
    using eval_formula.simps
    by simp
  also have "... = eval_formula (Not \<phi>) vI fI pI"
    using `simp_formula \<phi> = F` IH eval_formula.simps
    by simp  
  finally show ?thesis .
qed

(*
theorem eval_formula_simp_formula_equiv_eval_formula: "eval_formula (simp_formula \<phi>) vI fI pI = eval_formula \<phi> vI fI pI"
proof (induction \<phi> rule: simp_formula.induct)
  case (1 p args)
  then show ?case by simp
next
  case (2 f1 f2)
  then show ?case sorry
next
  case (3 f1 f2)
  then show ?case sorry
next
  case (4 f)
  then show ?case by (rule eval_formula_simp_formula_Not_equiv)
next
  case (5 t1 t2)
  then show ?case by simp
next
  case (6 v f)
  then show ?case sorry
next
  case (7 v f)
  then show ?case sorry
next
  case 8
  then show ?case by simp
next
  case 9
  then show ?case by simp
qed
*)

end