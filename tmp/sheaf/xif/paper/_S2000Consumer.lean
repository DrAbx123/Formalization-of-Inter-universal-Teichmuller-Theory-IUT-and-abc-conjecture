import tmp.sheaf.xif.paper.S2000CohomologicalPsiCnsActual

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual

namespace LeanFormal.IUT.XiFPaper.S2000Consumer

variable (p : Nat) [Fact (Nat.Prime p)]

#check PsiCnsCyclotome
#check PsiCnsCyclotomeTorsionEquiv
#check PsiCnsCoefficientAction
#check PsiCnsCohomology
#check PsiCnsKummer
#check PsiCnsKummerImage
#check PsiCnsUnitKummer
#check PsiCnsUnitKummer_injective
#check PsiCnsUnitKummerEquiv
#check PsiCnsKummerGroupification
#check PsiCnsKummerKernelInUnits
#check PsiCnsKummer_injective_of_kernelInUnits
#check PsiCnsKummerImage_equiv_of_kernelInUnits

example (h : PsiCnsKummerKernelInUnits p) :
    Nonempty (PsiCnsKummerImage p ≃* PsiCnsModel p) :=
  PsiCnsKummerImage_equiv_of_kernelInUnits p h

example : Function.Injective (PsiCnsUnitKummer p) :=
  PsiCnsUnitKummer_injective p

#print axioms PsiCnsUnitKummerEquiv
#print axioms PsiCnsKummerImage_equiv_of_kernelInUnits

end LeanFormal.IUT.XiFPaper.S2000Consumer
