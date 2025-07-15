theory FOF_Simplify
  imports Main FOF_Base
begin

lemma eval_formula_Not_Not: "eval_formula (Not (Not f)) vI fI pI = eval_formula f vI fI pI"
  by simp

lemma eval_formula_simp_formula_Or_equiv:
  assumes IH1: "eval_formula (simp_formula \<phi>1) vI fI pI = eval_formula \<phi>1 vI fI pI" 
      and IH2: "eval_formula (simp_formula \<phi>2) vI fI pI = eval_formula \<phi>2 vI fI pI"
    shows "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
proof (cases "simp_formula \<phi>1")
  case (Pred p1 args1)
  then show ?thesis
  proof (cases "simp_formula \<phi>2")
    case (Pred p2 args2)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Pred p1 args1) (Pred p2 args2)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Pred p1 args1)` `simp_formula \<phi>2 = (Pred p2 args2)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Pred p1 args1) vI fI pI) \<or> (eval_formula (Pred p2 args2) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Pred p1 args1)` `simp_formula \<phi>2 = (Pred p2 args2)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (And f1 f2)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Pred p1 args1) (And f1 f2)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Pred p1 args1)` `simp_formula \<phi>2 = (And f1 f2)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Pred p1 args1) vI fI pI) \<or> (eval_formula (And f1 f2) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Pred p1 args1)` `simp_formula \<phi>2 = (And f1 f2)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Or f1 f2)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Pred p1 args1) (Or f1 f2)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Pred p1 args1)` `simp_formula \<phi>2 = (Or f1 f2)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Pred p1 args1) vI fI pI) \<or> (eval_formula (Or f1 f2) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Pred p1 args1)` `simp_formula \<phi>2 = (Or f1 f2)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Not f)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Pred p1 args1) (Not f)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Pred p1 args1)` `simp_formula \<phi>2 = (Not f)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Pred p1 args1) vI fI pI) \<or> (eval_formula (Not f) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Pred p1 args1)` `simp_formula \<phi>2 = (Not f)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Equal t1 t2)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Pred p1 args1) (Equal t1 t2)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Pred p1 args1)` `simp_formula \<phi>2 = (Equal t1 t2)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Pred p1 args1) vI fI pI) \<or> (eval_formula (Equal t1 t2) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Pred p1 args1)` `simp_formula \<phi>2 = (Equal t1 t2)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Forall v f)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Pred p1 args1) (Forall v f)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Pred p1 args1)` `simp_formula \<phi>2 = (Forall v f)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Pred p1 args1) vI fI pI) \<or> (eval_formula (Forall v f) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Pred p1 args1)` `simp_formula \<phi>2 = (Forall v f)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Exists v f)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Pred p1 args1) (Exists v f)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Pred p1 args1)` `simp_formula \<phi>2 = (Exists v f)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Pred p1 args1) vI fI pI) \<or> (eval_formula (Exists v f) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Pred p1 args1)` `simp_formula \<phi>2 = (Exists v f)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case T
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = True"
      using simp_formula.simps `simp_formula \<phi>1 = (Pred p1 args1)` `simp_formula \<phi>2 = T` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Pred p1 args1) vI fI pI) \<or> (eval_formula T vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>2 = T` IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case F
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Pred p1 args1) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Pred p1 args1)` `simp_formula \<phi>2 = F` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Pred p1 args1) vI fI pI) \<or> (eval_formula F vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Pred p1 args1)` `simp_formula \<phi>2 = F` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  qed
next
  case (And f1 f2)
  then show ?thesis
  proof (cases "simp_formula \<phi>2")
    case (Pred p args)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (And f1 f2) (Pred p args)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (And f1 f2)` `simp_formula \<phi>2 = (Pred p args)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (And f1 f2) vI fI pI) \<or> (eval_formula (Pred p args) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (And f1 f2)` `simp_formula \<phi>2 = (Pred p args)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (And f3 f4)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (And f1 f2) (And f3 f4)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (And f1 f2)` `simp_formula \<phi>2 = (And f3 f4)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (And f1 f2) vI fI pI) \<or> (eval_formula (And f3 f4) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (And f1 f2)` `simp_formula \<phi>2 = (And f3 f4)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Or f3 f4)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (And f1 f2) (Or f3 f4)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (And f1 f2)` `simp_formula \<phi>2 = (Or f3 f4)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (And f1 f2) vI fI pI) \<or> (eval_formula (Or f3 f4) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (And f1 f2)` `simp_formula \<phi>2 = (Or f3 f4)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Not f)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (And f1 f2) (Not f)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (And f1 f2)` `simp_formula \<phi>2 = (Not f)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (And f1 f2) vI fI pI) \<or> (eval_formula (Not f) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (And f1 f2)` `simp_formula \<phi>2 = (Not f)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Equal t1 t2)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (And f1 f2) (Equal t1 t2)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (And f1 f2)` `simp_formula \<phi>2 = (Equal t1 t2)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (And f1 f2) vI fI pI) \<or> (eval_formula (Equal t1 t2) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (And f1 f2)` `simp_formula \<phi>2 = (Equal t1 t2)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Forall v f)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (And f1 f2) (Forall v f)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (And f1 f2)` `simp_formula \<phi>2 = (Forall v f)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (And f1 f2) vI fI pI) \<or> (eval_formula (Forall v f) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (And f1 f2)` `simp_formula \<phi>2 = (Forall v f)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Exists v f)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (And f1 f2) (Exists v f)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (And f1 f2)` `simp_formula \<phi>2 = (Exists v f)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (And f1 f2) vI fI pI) \<or> (eval_formula (Exists v f) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (And f1 f2)` `simp_formula \<phi>2 = (Exists v f)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case T
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = True"
      using simp_formula.simps `simp_formula \<phi>1 = (And f1 f2)` `simp_formula \<phi>2 = T` eval_formula.simps
      by simp
    also have "... = ((eval_formula (And f1 f2) vI fI pI) \<or> (eval_formula T vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>2 = T` IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case F
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (And f1 f2) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (And f1 f2)` `simp_formula \<phi>2 = F` eval_formula.simps
      by simp
    also have "... = ((eval_formula (And f1 f2) vI fI pI) \<or> (eval_formula F vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (And f1 f2)` `simp_formula \<phi>2 = F` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  qed
next
  case (Or f1 f2)
  then show ?thesis
  proof (cases "simp_formula \<phi>2")
    case (Pred p args)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Or f1 f2) (Pred p args)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Or f1 f2)` `simp_formula \<phi>2 = (Pred p args)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Or f1 f2) vI fI pI) \<or> (eval_formula (Pred p args) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Or f1 f2)` `simp_formula \<phi>2 = (Pred p args)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (And f3 f4)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Or f1 f2) (And f3 f4)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Or f1 f2)` `simp_formula \<phi>2 = (And f3 f4)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Or f1 f2) vI fI pI) \<or> (eval_formula (And f3 f4) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Or f1 f2)` `simp_formula \<phi>2 = (And f3 f4)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Or f3 f4)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Or f1 f2) (Or f3 f4)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Or f1 f2)` `simp_formula \<phi>2 = (Or f3 f4)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Or f1 f2) vI fI pI) \<or> (eval_formula (Or f3 f4) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Or f1 f2)` `simp_formula \<phi>2 = (Or f3 f4)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Not f)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Or f1 f2) (Not f)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Or f1 f2)` `simp_formula \<phi>2 = (Not f)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Or f1 f2) vI fI pI) \<or> (eval_formula (Not f) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Or f1 f2)` `simp_formula \<phi>2 = (Not f)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Equal t1 t2)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Or f1 f2) (Equal t1 t2)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Or f1 f2)` `simp_formula \<phi>2 = (Equal t1 t2)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Or f1 f2) vI fI pI) \<or> (eval_formula (Equal t1 t2) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Or f1 f2)` `simp_formula \<phi>2 = (Equal t1 t2)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Forall v f)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Or f1 f2) (Forall v f)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Or f1 f2)` `simp_formula \<phi>2 = (Forall v f)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Or f1 f2) vI fI pI) \<or> (eval_formula (Forall v f) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Or f1 f2)` `simp_formula \<phi>2 = (Forall v f)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Exists v f)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Or f1 f2) (Exists v f)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Or f1 f2)` `simp_formula \<phi>2 = (Exists v f)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Or f1 f2) vI fI pI) \<or> (eval_formula (Exists v f) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Or f1 f2)` `simp_formula \<phi>2 = (Exists v f)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case T
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = True"
      using simp_formula.simps `simp_formula \<phi>1 = (Or f1 f2)` `simp_formula \<phi>2 = T` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Or f1 f2) vI fI pI) \<or> (eval_formula T vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>2 = T` IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case F
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or f1 f2) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Or f1 f2)` `simp_formula \<phi>2 = F` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Or f1 f2) vI fI pI) \<or> (eval_formula F vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Or f1 f2)` `simp_formula \<phi>2 = F` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  qed
next
  case (Not f1)
  then show ?thesis
  proof (cases "simp_formula \<phi>2")
    case (Pred p args)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Not f1) (Pred p args)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Not f1)` `simp_formula \<phi>2 = (Pred p args)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Not f1) vI fI pI) \<or> (eval_formula (Pred p args) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Not f1)` `simp_formula \<phi>2 = (Pred p args)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (And f2 f3)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Not f1) (And f2 f3)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Not f1)` `simp_formula \<phi>2 = (And f2 f3)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Not f1) vI fI pI) \<or> (eval_formula (And f2 f3) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Not f1)` `simp_formula \<phi>2 = (And f2 f3)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Or f2 f3)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Not f1) (Or f2 f3)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Not f1)` `simp_formula \<phi>2 = (Or f2 f3)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Not f1) vI fI pI) \<or> (eval_formula (Or f2 f3) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Not f1)` `simp_formula \<phi>2 = (Or f2 f3)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Not f2)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Not f1) (Not f2)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Not f1)` `simp_formula \<phi>2 = (Not f2)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Not f1) vI fI pI) \<or> (eval_formula (Not f2) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Not f1)` `simp_formula \<phi>2 = (Not f2)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Equal t1 t2)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Not f1) (Equal t1 t2)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Not f1)` `simp_formula \<phi>2 = (Equal t1 t2)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Not f1) vI fI pI) \<or> (eval_formula (Equal t1 t2) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Not f1)` `simp_formula \<phi>2 = (Equal t1 t2)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Forall v f)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Not f1) (Forall v f)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Not f1)` `simp_formula \<phi>2 = (Forall v f)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Not f1) vI fI pI) \<or> (eval_formula (Forall v f) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Not f1)` `simp_formula \<phi>2 = (Forall v f)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Exists v f)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Not f1) (Exists v f)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Not f1)` `simp_formula \<phi>2 = (Exists v f)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Not f1) vI fI pI) \<or> (eval_formula (Exists v f) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Not f1)` `simp_formula \<phi>2 = (Exists v f)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case T
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = True"
      using simp_formula.simps `simp_formula \<phi>1 = (Not f1)` `simp_formula \<phi>2 = T` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Not f1) vI fI pI) \<or> (eval_formula T vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>2 = T` IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case F
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Not f1) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Not f1)` `simp_formula \<phi>2 = F` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Not f1) vI fI pI) \<or> (eval_formula F vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Not f1)` `simp_formula \<phi>2 = F` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  qed
next
  case (Equal t1 t2)
  then show ?thesis
  proof (cases "simp_formula \<phi>2")
    case (Pred p args)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Equal t1 t2) (Pred p args)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Equal t1 t2)` `simp_formula \<phi>2 = (Pred p args)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Equal t1 t2) vI fI pI) \<or> (eval_formula (Pred p args) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Equal t1 t2)` `simp_formula \<phi>2 = (Pred p args)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (And f1 f2)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Equal t1 t2) (And f1 f2)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Equal t1 t2)` `simp_formula \<phi>2 = (And f1 f2)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Equal t1 t2) vI fI pI) \<or> (eval_formula (And f1 f2) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Equal t1 t2)` `simp_formula \<phi>2 = (And f1 f2)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Or f1 f2)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Equal t1 t2) (Or f1 f2)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Equal t1 t2)` `simp_formula \<phi>2 = (Or f1 f2)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Equal t1 t2) vI fI pI) \<or> (eval_formula (Or f1 f2) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Equal t1 t2)` `simp_formula \<phi>2 = (Or f1 f2)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Not f)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Equal t1 t2) (Not f)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Equal t1 t2)` `simp_formula \<phi>2 = (Not f)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Equal t1 t2) vI fI pI) \<or> (eval_formula (Not f) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Equal t1 t2)` `simp_formula \<phi>2 = (Not f)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Equal t3 t4)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Equal t1 t2) (Equal t3 t4)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Equal t1 t2)` `simp_formula \<phi>2 = (Equal t3 t4)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Equal t1 t2) vI fI pI) \<or> (eval_formula (Equal t3 t4) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Equal t1 t2)` `simp_formula \<phi>2 = (Equal t3 t4)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Forall v f)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Equal t1 t2) (Forall v f)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Equal t1 t2)` `simp_formula \<phi>2 = (Forall v f)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Equal t1 t2) vI fI pI) \<or> (eval_formula (Forall v f) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Equal t1 t2)` `simp_formula \<phi>2 = (Forall v f)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Exists v f)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Equal t1 t2) (Exists v f)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Equal t1 t2)` `simp_formula \<phi>2 = (Exists v f)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Equal t1 t2) vI fI pI) \<or> (eval_formula (Exists v f) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Equal t1 t2)` `simp_formula \<phi>2 = (Exists v f)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case T
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = True"
      using simp_formula.simps `simp_formula \<phi>1 = (Equal t1 t2)` `simp_formula \<phi>2 = T` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Equal t1 t2) vI fI pI) \<or> (eval_formula T vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>2 = T` IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case F
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Equal t1 t2) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Equal t1 t2)` `simp_formula \<phi>2 = F` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Equal t1 t2) vI fI pI) \<or> (eval_formula F vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Equal t1 t2)` `simp_formula \<phi>2 = F` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  qed
next
  case (Forall v1 f1)
  then show ?thesis
  proof (cases "simp_formula \<phi>2")
    case (Pred p args)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Forall v1 f1) (Pred p args)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Forall v1 f1)` `simp_formula \<phi>2 = (Pred p args)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Forall v1 f1) vI fI pI) \<or> (eval_formula (Pred p args) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Forall v1 f1)` `simp_formula \<phi>2 = (Pred p args)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (And f2 f3)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Forall v1 f1) (And f2 f3)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Forall v1 f1)` `simp_formula \<phi>2 = (And f2 f3)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Forall v1 f1) vI fI pI) \<or> (eval_formula (And f2 f3) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Forall v1 f1)` `simp_formula \<phi>2 = (And f2 f3)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Or f2 f3)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Forall v1 f1) (Or f2 f3)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Forall v1 f1)` `simp_formula \<phi>2 = (Or f2 f3)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Forall v1 f1) vI fI pI) \<or> (eval_formula (Or f2 f3) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Forall v1 f1)` `simp_formula \<phi>2 = (Or f2 f3)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Not f)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Forall v1 f1) (Not f)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Forall v1 f1)` `simp_formula \<phi>2 = (Not f)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Forall v1 f1) vI fI pI) \<or> (eval_formula (Not f) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Forall v1 f1)` `simp_formula \<phi>2 = (Not f)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Equal t1 t2)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Forall v1 f1) (Equal t1 t2)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Forall v1 f1)` `simp_formula \<phi>2 = (Equal t1 t2)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Forall v1 f1) vI fI pI) \<or> (eval_formula (Equal t1 t2) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Forall v1 f1)` `simp_formula \<phi>2 = (Equal t1 t2)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Forall v2 f2)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Forall v1 f1) (Forall v2 f2)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Forall v1 f1)` `simp_formula \<phi>2 = (Forall v2 f2)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Forall v1 f1) vI fI pI) \<or> (eval_formula (Forall v2 f2) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Forall v1 f1)` `simp_formula \<phi>2 = (Forall v2 f2)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Exists v2 f2)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Forall v1 f1) (Exists v2 f2)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Forall v1 f1)` `simp_formula \<phi>2 = (Exists v2 f2)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Forall v1 f1) vI fI pI) \<or> (eval_formula (Exists v2 f2) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Forall v1 f1)` `simp_formula \<phi>2 = (Exists v2 f2)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case T
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = True"
      using simp_formula.simps `simp_formula \<phi>1 = (Forall v1 f1)` `simp_formula \<phi>2 = T` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Forall v1 f1) vI fI pI) \<or> (eval_formula T vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>2 = T` IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case F
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Forall v1 f1) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Forall v1 f1)` `simp_formula \<phi>2 = F` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Forall v1 f1) vI fI pI) \<or> (eval_formula F vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Forall v1 f1)` `simp_formula \<phi>2 = F` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  qed
next
  case (Exists v1 f1)
  then show ?thesis
  proof (cases "simp_formula \<phi>2")
    case (Pred p args)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Exists v1 f1) (Pred p args)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Exists v1 f1)` `simp_formula \<phi>2 = (Pred p args)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Exists v1 f1) vI fI pI) \<or> (eval_formula (Pred p args) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Exists v1 f1)` `simp_formula \<phi>2 = (Pred p args)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (And f2 f3)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Exists v1 f1) (And f2 f3)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Exists v1 f1)` `simp_formula \<phi>2 = (And f2 f3)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Exists v1 f1) vI fI pI) \<or> (eval_formula (And f2 f3) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Exists v1 f1)` `simp_formula \<phi>2 = (And f2 f3)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Or f2 f3)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Exists v1 f1) (Or f2 f3)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Exists v1 f1)` `simp_formula \<phi>2 = (Or f2 f3)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Exists v1 f1) vI fI pI) \<or> (eval_formula (Or f2 f3) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Exists v1 f1)` `simp_formula \<phi>2 = (Or f2 f3)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Not f)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Exists v1 f1) (Not f)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Exists v1 f1)` `simp_formula \<phi>2 = (Not f)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Exists v1 f1) vI fI pI) \<or> (eval_formula (Not f) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Exists v1 f1)` `simp_formula \<phi>2 = (Not f)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Equal t1 t2)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Exists v1 f1) (Equal t1 t2)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Exists v1 f1)` `simp_formula \<phi>2 = (Equal t1 t2)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Exists v1 f1) vI fI pI) \<or> (eval_formula (Equal t1 t2) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Exists v1 f1)` `simp_formula \<phi>2 = (Equal t1 t2)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Forall v2 f2)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Exists v1 f1) (Forall v2 f2)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Exists v1 f1)` `simp_formula \<phi>2 = (Forall v2 f2)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Exists v1 f1) vI fI pI) \<or> (eval_formula (Forall v2 f2) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Exists v1 f1)` `simp_formula \<phi>2 = (Forall v2 f2)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Exists v2 f2)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or (Exists v1 f1) (Exists v2 f2)) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Exists v1 f1)` `simp_formula \<phi>2 = (Exists v2 f2)` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Exists v1 f1) vI fI pI) \<or> (eval_formula (Exists v2 f2) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Exists v1 f1)` `simp_formula \<phi>2 = (Exists v2 f2)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case T
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = True"
      using simp_formula.simps `simp_formula \<phi>1 = (Exists v1 f1)` `simp_formula \<phi>2 = T` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Exists v1 f1) vI fI pI) \<or> (eval_formula T vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>2 = T` IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case F
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Exists v1 f1) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = (Exists v1 f1)` `simp_formula \<phi>2 = F` eval_formula.simps
      by simp
    also have "... = ((eval_formula (Exists v1 f1) vI fI pI) \<or> (eval_formula F vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = (Exists v1 f1)` `simp_formula \<phi>2 = F` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  qed
next
  case T
  then show ?thesis
  proof (cases "simp_formula \<phi>2")
    case (Pred p args)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = True"
      using simp_formula.simps `simp_formula \<phi>1 = T` `simp_formula \<phi>2 = (Pred p args)` eval_formula.simps
      by simp
    also have "... = ((eval_formula T vI fI pI) \<or> (eval_formula (Pred p args) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = T` IH1 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (And f1 f2)
        have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = True"
      using simp_formula.simps `simp_formula \<phi>1 = T` `simp_formula \<phi>2 = (And f1 f2)` eval_formula.simps
      by simp
    also have "... = ((eval_formula T vI fI pI) \<or> (eval_formula (And f1 f2) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = T` IH1 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Or f1 f2)
        have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = True"
      using simp_formula.simps `simp_formula \<phi>1 = T` `simp_formula \<phi>2 = (Or f1 f2)` eval_formula.simps
      by simp
    also have "... = ((eval_formula T vI fI pI) \<or> (eval_formula (Or f1 f2) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = T` IH1 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Not f)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = True"
      using simp_formula.simps `simp_formula \<phi>1 = T` `simp_formula \<phi>2 = (Not f)` eval_formula.simps
      by simp
    also have "... = ((eval_formula T vI fI pI) \<or> (eval_formula (Not f) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = T` IH1 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Equal t1 t2)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = True"
      using simp_formula.simps `simp_formula \<phi>1 = T` `simp_formula \<phi>2 = (Equal t1 t2)` eval_formula.simps
      by simp
    also have "... = ((eval_formula T vI fI pI) \<or> (eval_formula (Equal t1 t2) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = T` IH1 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Forall v f)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = True"
      using simp_formula.simps `simp_formula \<phi>1 = T` `simp_formula \<phi>2 = (Forall v f)` eval_formula.simps
      by simp
    also have "... = ((eval_formula T vI fI pI) \<or> (eval_formula (Forall v f) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = T` IH1 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Exists v f)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = True"
      using simp_formula.simps `simp_formula \<phi>1 = T` `simp_formula \<phi>2 = (Exists v f)` eval_formula.simps
      by simp
    also have "... = ((eval_formula T vI fI pI) \<or> (eval_formula (Exists v f) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = T` IH1 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case T
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = True"
      using simp_formula.simps `simp_formula \<phi>1 = T` `simp_formula \<phi>2 = T` eval_formula.simps
      by simp
    also have "... = ((eval_formula T vI fI pI) \<or> (eval_formula T vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = T` IH1 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case F
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = True"
      using simp_formula.simps `simp_formula \<phi>1 = T` `simp_formula \<phi>2 = F` eval_formula.simps
      by simp
    also have "... = ((eval_formula T vI fI pI) \<or> (eval_formula F vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = T` IH1 eval_formula.simps 
      by simp
    finally show ?thesis .
  qed
next
  case F
  then show ?thesis
  proof (cases "simp_formula \<phi>2")
    case (Pred p args)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Pred p args) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = F` `simp_formula \<phi>2 = (Pred p args)` eval_formula.simps
      by simp
    also have "... = ((eval_formula F vI fI pI) \<or> (eval_formula (Pred p args) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = F` `simp_formula \<phi>2 = (Pred p args)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (And f1 f2)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (And f1 f2) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = F` `simp_formula \<phi>2 = (And f1 f2)` eval_formula.simps
      by simp
    also have "... = ((eval_formula F vI fI pI) \<or> (eval_formula (And f1 f2) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = F` `simp_formula \<phi>2 = (And f1 f2)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Or f1 f2)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Or f1 f2) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = F` `simp_formula \<phi>2 = (Or f1 f2)` eval_formula.simps
      by simp
    also have "... = ((eval_formula F vI fI pI) \<or> (eval_formula (Or f1 f2) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = F` `simp_formula \<phi>2 = (Or f1 f2)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Not f)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Not f) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = F` `simp_formula \<phi>2 = (Not f)` eval_formula.simps
      by simp
    also have "... = ((eval_formula F vI fI pI) \<or> (eval_formula (Not f) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = F` `simp_formula \<phi>2 = (Not f)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Equal t1 t2)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Equal t1 t2) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = F` `simp_formula \<phi>2 = (Equal t1 t2)` eval_formula.simps
      by simp
    also have "... = ((eval_formula F vI fI pI) \<or> (eval_formula (Equal t1 t2) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = F` `simp_formula \<phi>2 = (Equal t1 t2)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Forall v f)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Forall v f) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = F` `simp_formula \<phi>2 = (Forall v f)` eval_formula.simps
      by simp
    also have "... = ((eval_formula F vI fI pI) \<or> (eval_formula (Forall v f) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = F` `simp_formula \<phi>2 = (Forall v f)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case (Exists v f)
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = eval_formula (Exists v f) vI fI pI"
      using simp_formula.simps `simp_formula \<phi>1 = F` `simp_formula \<phi>2 = (Exists v f)` eval_formula.simps
      by simp
    also have "... = ((eval_formula F vI fI pI) \<or> (eval_formula (Exists v f) vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = F` `simp_formula \<phi>2 = (Exists v f)` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case T
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = True"
      using simp_formula.simps `simp_formula \<phi>1 = F` `simp_formula \<phi>2 = T` eval_formula.simps
      by simp
    also have "... = ((eval_formula F vI fI pI) \<or> (eval_formula T vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>2 = T` IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  next
    case F
    have "eval_formula (simp_formula (Or \<phi>1 \<phi>2)) vI fI pI = False"
      using simp_formula.simps `simp_formula \<phi>1 = F` `simp_formula \<phi>2 = F` eval_formula.simps
      by simp
    also have "... = ((eval_formula F vI fI pI) \<or> (eval_formula F vI fI pI))"
      using eval_formula.simps
      by simp
    also have "... = eval_formula (Or \<phi>1 \<phi>2) vI fI pI"
      using `simp_formula \<phi>1 = F` `simp_formula \<phi>2 = F` IH1 IH2 eval_formula.simps
      by simp
    finally show ?thesis .
  qed
qed

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

theorem eval_formula_simp_formula_equiv_eval_formula: "eval_formula (simp_formula \<phi>) vI fI pI = eval_formula \<phi> vI fI pI"
proof (induction \<phi> rule: simp_formula.induct)
  case (1 p args)
  then show ?case by simp
next
  case (2 f1 f2)
  then show ?case sorry
next
  case (3 f1 f2)
  then show ?case by (rule eval_formula_simp_formula_Or_equiv)
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

end