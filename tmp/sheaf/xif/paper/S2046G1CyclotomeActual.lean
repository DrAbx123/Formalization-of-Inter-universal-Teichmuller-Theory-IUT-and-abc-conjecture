import tmp.sheaf.xif.paper.S2039ActualPsiCns
import tmp.sheaf.xif.paper.S2046M3M4S2091Port

-- S2046 G1: cyclotome module comparison and exact topological G_v-module data.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2046G1CyclotomeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2039ActualPsiCns

variable (p : Nat) [Fact (Nat.Prime p)]

/-- Exact G1 comparison input: S2017's muHatComparison. -/
abbrev S2046G1MuHatComparisonRequired : Prop := muHatComparison p

/-- Actual module-level cyclotome equivalence from muHatComparison. -/
noncomputable def S2046G1ModuleEquivOfComparison
    (h : S2046G1MuHatComparisonRequired p) :
    muHatZ p ≃* PsiCnsCyclotome p :=
  Classical.choice (PsiCnsCyclotome_equiv_of_cyclotomeComparison p h)

/-- The actual G_v-action on the S2000 cyclotome. -/
noncomputable abbrev S2046G1PsiCnsAction :
    Gv p →* MulAut (PsiCnsCyclotome p) :=
  (PsiCnsCoefficientAction p).automorphism

/-- Exact G1 topological module data: an action on the S2017 cyclotome and
an equivariant module equivalence.  No inhabitant is asserted. -/
structure S2046G1TopologicalModuleData where
  muHatAction : Gv p →* MulAut (muHatZ p)
  equiv : muHatZ p ≃* PsiCnsCyclotome p
  equivariant :
    ∀ (g : Gv p) (x : muHatZ p),
      equiv (muHatAction g x) = S2046G1PsiCnsAction p g (equiv x)

abbrev S2046G1TopologicalModuleRequired : Type :=
  S2046G1TopologicalModuleData p

/-- Actual S2000 torsion-corestriction equivalence. -/
noncomputable abbrev S2046G1TorsionEquiv :
    PsiCnsCyclotome p ≃* PsiCnsTorsionCyclotome p :=
  PsiCnsCyclotomeTorsionEquiv p

#check S2046G1MuHatComparisonRequired
#check S2046G1ModuleEquivOfComparison
#check S2046G1PsiCnsAction
#check S2046G1TopologicalModuleData
#check S2046G1TopologicalModuleRequired
#check S2046G1TorsionEquiv

#print axioms S2046G1ModuleEquivOfComparison
#print axioms S2046G1TorsionEquiv

end LeanFormal.IUT.XiFPaper.S2046G1CyclotomeActual

end