import tmp.sheaf.xif.paper.S2006KummerKernelActual

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2006KummerKernelActual

namespace LeanFormal.IUT.XiFPaper.S2006Consumer

variable (p : Nat) [Fact (Nat.Prime p)]

#check PsiCnsKummerKernelInUnits_holds
#check PsiCnsKummer_injective
#check PsiCnsKummerImage_equiv
#check PsiCnsKummer_injective_of_kernelInUnits
#check PsiCnsKummerKernelInUnits_iff_injective

example : PsiCnsKummerKernelInUnits p := PsiCnsKummerKernelInUnits_holds p

example : Function.Injective (PsiCnsKummer p) := PsiCnsKummer_injective p

example : Nonempty (PsiCnsKummerImage p ≃* PsiCnsModel p) := PsiCnsKummerImage_equiv p

example : PsiCnsKummerKernelInUnits p ↔ Function.Injective (PsiCnsKummer p) :=
  PsiCnsKummerKernelInUnits_iff_injective p

#print axioms PsiCnsKummerKernelInUnits_holds
#print axioms PsiCnsKummer_injective
#print axioms PsiCnsKummerImage_equiv

end LeanFormal.IUT.XiFPaper.S2006Consumer
