import tmp.sheaf.xif.paper.S2046G1CyclotomeActual

-- S2131: G1 topological cyclotome module.  The actual module equivalence
-- from muHatComparison is available; the topological G_v-action on muHatZ
-- and its equivariance remain the exact first missing.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2131G1TopologicalActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2039ActualPsiCns
open LeanFormal.IUT.XiFPaper.S2046G1CyclotomeActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- Exact G1 action first missing: a topological G_v-action on muHatZ. -/
abbrev S2131MuHatActionRequired : Type :=
  Gv p →* MulAut (muHatZ p)

/-- The module comparison input, S2017's muHatComparison. -/
abbrev S2131MuHatComparisonRequired : Prop := muHatComparison p

/-- Actual module equivalence from muHatComparison. -/
noncomputable def S2131ModuleEquivOfComparison
    (h : S2131MuHatComparisonRequired p) :
    muHatZ p ≃* PsiCnsCyclotome p :=
  S2046G1ModuleEquivOfComparison (p := p) h

/-- The exact topological module data: action, module comparison, equivariance. -/
structure S2131TopologicalModuleData where
  muHatAction : Gv p →* MulAut (muHatZ p)
  equiv : muHatZ p ≃* PsiCnsCyclotome p
  equivariant :
    ∀ (g : Gv p) (x : muHatZ p),
      equiv (muHatAction g x) =
        (PsiCnsCoefficientAction p).automorphism g (equiv x)

abbrev S2131TopologicalModuleRequired : Type :=
  S2131TopologicalModuleData p

/-- Conditional construction: action + equivariant comparison give the data. -/
noncomputable def S2131TopologicalModuleDataOf
    (a : S2131MuHatActionRequired p)
    (h : S2131MuHatComparisonRequired p)
    (heq : ∀ (g : Gv p) (x : muHatZ p),
      S2131ModuleEquivOfComparison (p := p) h (a g x) =
        (PsiCnsCoefficientAction p).automorphism g
          (S2131ModuleEquivOfComparison (p := p) h x)) :
    S2131TopologicalModuleData p where
  muHatAction := a
  equiv := S2131ModuleEquivOfComparison (p := p) h
  equivariant := heq

#check S2131MuHatActionRequired
#check S2131MuHatComparisonRequired
#check S2131ModuleEquivOfComparison
#check S2131TopologicalModuleData
#check S2131TopologicalModuleRequired
#check S2131TopologicalModuleDataOf

#print axioms S2131ModuleEquivOfComparison
#print axioms S2131TopologicalModuleDataOf

end LeanFormal.IUT.XiFPaper.S2131G1TopologicalActual

end