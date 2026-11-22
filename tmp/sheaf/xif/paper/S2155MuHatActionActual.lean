import tmp.sheaf.xif.paper.S2131G1TopologicalActual

-- S2155: topological action on muHatZ.  The action is reduced to an
-- action on muQZ plus its discrete topological structure; both remain
-- exact missing.  No M2c/M3 assumption, no fake.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2155MuHatActionActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2039ActualPsiCns
open LeanFormal.IUT.XiFPaper.S2046G1CyclotomeActual
open LeanFormal.IUT.XiFPaper.S2131G1TopologicalActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- Exact topology first missing on muQZ. -/
abbrev S2155MuQZTopologyRequired : Type :=
  TopologicalSpace (Multiplicative (muQZ p))

/-- Exact algebraic action first missing on muQZ. -/
abbrev S2155MuQZActionRequired : Type :=
  Gv p →* MulAut (Multiplicative (muQZ p))

/-- Exact topological action first missing on muHatZ. -/
abbrev S2155MuHatActionRequired : Type :=
  Gv p →* MulAut (muHatZ p)

/-- Exact discrete-continuity first missing, expressed as the topological
action data to be supplied on muQZ. -/
structure S2155MuQZContinuousActionRequired where
  top : TopologicalSpace (Multiplicative (muQZ p))
  discrete : @DiscreteTopology (Multiplicative (muQZ p)) top
  automorphism : Gv p →* MulAut (Multiplicative (muQZ p))
  continuous_action :
    letI := top
    Continuous fun q : Gv p × Multiplicative (muQZ p) =>
      automorphism q.1 q.2

/-- Conditional G1 topological module data from the muHat action, the
module comparison, and equivariance. -/
noncomputable def S2155TopologicalModuleDataOf
    (a : S2155MuHatActionRequired p)
    (h : muHatComparison p)
    (heq : ∀ (g : Gv p) (x : muHatZ p),
      S2131ModuleEquivOfComparison (p := p) h (a g x) =
        (PsiCnsCoefficientAction p).automorphism g
          (S2131ModuleEquivOfComparison (p := p) h x)) :
    S2131TopologicalModuleData p where
  muHatAction := a
  equiv := S2131ModuleEquivOfComparison (p := p) h
  equivariant := heq

#check S2155MuQZTopologyRequired
#check S2155MuQZActionRequired
#check S2155MuHatActionRequired
#check S2155MuQZContinuousActionRequired
#check S2155TopologicalModuleDataOf

#print axioms S2155TopologicalModuleDataOf

end LeanFormal.IUT.XiFPaper.S2155MuHatActionActual

end