/- Small p-adic donor for U-C K-side letters: if the local different ideal is trivial, then
the normalized order of the local different generator is zero. -/
import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentNormOrder
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualTensorInclusion
import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentUpperBound
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1LocalDifferentOrderZeroActual

open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.IntegralTraceDualTensorInclusion
open LeanFormal.IUT.LocalDifferentUpperBound
open LeanFormal.IUT.LocalDifferentNormOrder
open UniqueFactorizationMonoid

/-- If the local different ideal is trivial (top), then the DVR order of the local different
generator is zero. -/
theorem localDifferentOrder_eq_zero_of_localDifferentIdeal_eq_top {p : Nat} [Fact p.Prime]
    {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L] [IsUltrametricDist L]
    [ProperSpace L] [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    (h : localDifferentIdeal (p := p) (L := L) = ⊤) :
    localDifferentOrder (p := p) (L := L) = 0 := by
  haveI : IsDiscreteValuationRing (Integers L) := integersIsDiscreteValuationRing (p := p) (L := L)
  have hdiff : differentIdeal ℤ_[p] (Integers L) = ⊤ := by
    simpa [localDifferentIdeal] using h
  rw [localDifferentOrder_eq_factorCount (K := L), hdiff]
  have htop : normalizedFactors (⊤ : Ideal (Integers L)) = 0 := by
    rw [← Ideal.one_eq_top (R := Integers L)]
    exact UniqueFactorizationMonoid.normalizedFactors_one
  rw [htop]
  simp

/-- If the local different ideal is trivial, then the paper-normalized different order is 0. -/
theorem localDifferentPaperOrder_eq_zero_of_localDifferentIdeal_eq_top {p : Nat} [Fact p.Prime]
    {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L] [IsUltrametricDist L]
    [ProperSpace L] [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    (h : localDifferentIdeal (p := p) (L := L) = ⊤) :
    localDifferentPaperOrder (p := p) (L := L) = 0 := by
  simp only [localDifferentPaperOrder]
  rw [localDifferentOrder_eq_zero_of_localDifferentIdeal_eq_top h]
  simp

/-- The normalized norm-order of the local different generator vanishes when the local
different ideal is trivial. -/
theorem localNormOrder_differentGenerator_eq_zero_of_localDifferentIdeal_eq_top {p : Nat}
    [Fact p.Prime] {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L]
    [IsUltrametricDist L] [ProperSpace L] [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    (h : localDifferentIdeal (p := p) (L := L) = ⊤) :
    localNormOrder p (localDifferentGenerator (p := p) (L := L) : L) = 0 := by
  rw [localNormOrder_differentGenerator_eq_paperOrder (K := L)]
  exact localDifferentPaperOrder_eq_zero_of_localDifferentIdeal_eq_top h

#print axioms localDifferentOrder_eq_zero_of_localDifferentIdeal_eq_top
#print axioms localDifferentPaperOrder_eq_zero_of_localDifferentIdeal_eq_top
#print axioms localNormOrder_differentGenerator_eq_zero_of_localDifferentIdeal_eq_top
end LeanFormal.IUT.XiFPaper.Mzk1G1LocalDifferentOrderZeroActual
