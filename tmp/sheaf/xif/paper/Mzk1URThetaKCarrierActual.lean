/- U-R C2 (P) K-side carrier toolkit (kurt).

Carrier-independent piece: p6Phi contains the identity linear equivalence.
No sorry, no axioms; this file only uses maxHeartbeats 1000000 (paper-level
elaboration budget, same reason as PaperLevelXiFTargetActual). -/
import tmp.sheaf.xif.paper.Mzk1P6PhiActionFamilyActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaKCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P6PhiActionFamilyActual

universe u v w

/-- The identity linear equivalence belongs to the actual p6Phi action family. -/
theorem urP6Phi_id_mem {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {ι : Type v} [Fintype ι] {V : ι → Type w} [∀ i, Fintype (V i)] [DecidableEq ι]
    [∀ i, DecidableEq (V i)]
    (places : (i : ι) → V i → FinitePlaceAtPrime K p)
    (tuple : (i : ι) → V i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)] :
    (LinearEquiv.refl ℚ_[p] (ArithmeticTensorTupleBlock places tuple)) ∈
      p6Phi places tuple := by
  intro u hu
  exact hu

#print axioms urP6Phi_id_mem

end LeanFormal.IUT.XiFPaper.Mzk1URThetaKCarrierActual
end