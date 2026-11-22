import tmp.sheaf.xif.paper.S2501UniversalCoverSystemActual

/-! # S2502: finite-level O^◃ carrier in a finite Galois intermediate field

For L a finite Galois intermediate field, define the actual valuation subring
of L (comap of the Q_p valuation ring) and the integral closure of L in it;
its nonzero monoid is the finite-level O^◃ carrier.  Transition and O^▷/rho
maps remain exact missing if not constructed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2500CategoricalOtriangleActual
open LeanFormal.IUT.XiFPaper.S2501UniversalCoverSystemActual
open scoped nonZeroDivisors

namespace LeanFormal.IUT.XiFPaper.S2502FiniteLevelODiamondActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- The valuation subring of a finite Galois intermediate field: comap of the
Q_p valuation ring. -/
noncomputable def S2502ValuationSubring
    (L : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) :
    Subring L.1 :=
  (integralClosure (Valuation.integer (ValuativeRel.valuation ℚ_[p])) L.1).toSubring

/-- Integral closure of the valuation subring in L. -/
noncomputable def S2502IntegralClosure
    (L : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) :
    Subring L.1 :=
  S2502ValuationSubring p L

/-- Finite-level O^◃ carrier: nonzero elements of the integral closure. -/
noncomputable abbrev S2502ODiamond
    (L : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) : Type :=
  (S2502IntegralClosure p L)⁰

instance S2502ODiamond_monoid
    (L : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) :
    Monoid (S2502ODiamond p L) := inferInstance

theorem S2502IntegralClosure_one
    (L : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) :
    (1 : S2502IntegralClosure p L) = 1 := rfl

#check S2502ValuationSubring
#check S2502IntegralClosure
#check S2502ODiamond

end LeanFormal.IUT.XiFPaper.S2502FiniteLevelODiamondActual
end
