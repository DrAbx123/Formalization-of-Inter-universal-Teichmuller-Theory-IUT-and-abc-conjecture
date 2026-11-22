/- R5 step 4: fraction-ring finrank identification (retry 2)
  finrank (FractionRing Z_p) (FractionRing (Integers L)) = finrank Q_p L

Reuse: Algebra.finrank_eq_of_equiv_equiv, FractionRing.algEquiv,
LeanFormal.IUT.LocalDifferentUpperBound.fractionRing_integer_degree_eq.
-/
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualTensorInclusion
import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentUpperBound
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic
noncomputable section
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FractionRingFinrankActual

open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.IntegralTraceDualTensorInclusion
open LeanFormal.IUT.LocalDifferentUpperBound

variable {p : Nat} [Fact p.Prime]
variable {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L] [IsUltrametricDist L]
  [ProperSpace L] [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]

/-- Ring equiv between the two fraction rings of the base. -/
noncomputable def fracEquiv : FractionRing ℤ_[p] ≃+* FractionRing (Integers ℚ_[p]) :=
  (FractionRing.algEquiv ℤ_[p] ℚ_[p]).toRingEquiv.trans
    (FractionRing.algEquiv (Integers ℚ_[p]) ℚ_[p]).symm.toRingEquiv

/-- The base fraction-ring finrank is independent of the chosen model of Q_p. -/
theorem finrank_fractionRing_eq :
    Module.finrank (FractionRing ℤ_[p]) (FractionRing (Integers L)) =
      Module.finrank (FractionRing (Integers ℚ_[p])) (FractionRing (Integers L)) := by
  refine Algebra.finrank_eq_of_equiv_equiv fracEquiv (RingEquiv.refl _) ?_
  ext x
  apply (FractionRing.algEquiv (Integers L) L).injective
  induction x using Localization.induction_on with
  | H a =>
      rcases a with ⟨a, b⟩
      simp [fracEquiv, map_div₀, IsFractionRing.algEquiv_commutes]

/-- Final identification with the field degree. -/
theorem finrank_fractionRing_eq_finrank :
    Module.finrank (FractionRing ℤ_[p]) (FractionRing (Integers L)) =
      Module.finrank ℚ_[p] L := by
  rw [finrank_fractionRing_eq]
  exact fractionRing_integer_degree_eq (K := ℚ_[p]) (L := L)

#print axioms finrank_fractionRing_eq
#print axioms finrank_fractionRing_eq_finrank
end LeanFormal.IUT.XiFPaper.Mzk1G1FractionRingFinrankActual
