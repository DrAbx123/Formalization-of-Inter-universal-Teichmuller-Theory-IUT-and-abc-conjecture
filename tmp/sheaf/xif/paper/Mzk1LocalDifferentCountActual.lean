/- U-R/U-C count bridge (kurt): local different paper order = normalized-factor
count of the local different ideal at the maximal ideal.  Pure Mathlib argument. -/
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualTensorInclusion
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1LocalDifferentCountActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IntegralTraceDualTensorInclusion
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open Ideal IsLocalRing

universe u

variable {p : ℕ} [Fact p.Prime]
variable {L : Type u} [NormedField L] [CharZero L] [CompleteSpace L]
  [IsUltrametricDist L] [ProperSpace L] [NormedAlgebra ℚ_[p] L]
  [FiniteDimensional ℚ_[p] L]

theorem localDifferentOrder_eq_count
    [IsDiscreteValuationRing (Integers L)] [IsDedekindDomain (Integers L)] :
    localDifferentOrder (p := p) (L := L) =
      (UniqueFactorizationMonoid.normalizedFactors
        (localDifferentIdeal (p := p) (L := L))).count (maximalIdeal (Integers L)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Integers L)
  have hgen_ne : localDifferentGenerator (p := p) (L := L) ≠ 0 :=
    localDifferentGenerator_ne_zero (p := p) (L := L)
  obtain ⟨n, u, hnu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hgen_ne hπ
  have horder : localDifferentOrder (p := p) (L := L) = n := by
    unfold localDifferentOrder
    rw [hnu, IsDiscreteValuationRing.addVal_def' u hπ n]
    simp
  have hmax : maximalIdeal (Integers L) = span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hideal : localDifferentIdeal (p := p) (L := L) =
      maximalIdeal (Integers L) ^ n := by
    rw [← localDifferentGenerator_span_eq (p := p) (L := L), hnu,
      Ideal.span_singleton_mul_left_unit u.isUnit, hmax, ← Ideal.span_singleton_pow]
  have hP0 : maximalIdeal (Integers L) ≠ ⊥ :=
    IsDiscreteValuationRing.not_a_field (Integers L)
  have hPprime : Prime (maximalIdeal (Integers L)) :=
    Ideal.prime_of_isPrime hP0 ((maximalIdeal.isMaximal (Integers L)).isPrime)
  have hPirr : Irreducible (maximalIdeal (Integers L)) := hPprime.irreducible
  have hcount : (UniqueFactorizationMonoid.normalizedFactors
      (maximalIdeal (Integers L) ^ n)).count (maximalIdeal (Integers L)) = n := by
    rw [Irreducible.normalizedFactors_pow hPirr n]
    rw [show normalize (maximalIdeal (Integers L)) = maximalIdeal (Integers L) from
      normalize_eq _]
    exact Multiset.count_replicate_self _ _
  rw [horder, hideal, hcount]

theorem localDifferentPaperOrder_eq_count
    [IsDiscreteValuationRing (Integers L)] [IsDedekindDomain (Integers L)] :
    localDifferentPaperOrder (p := p) (L := L) =
      ((UniqueFactorizationMonoid.normalizedFactors
          (localDifferentIdeal (p := p) (L := L))).count (maximalIdeal (Integers L)) : ℝ) /
        (logShellRamificationExponent (K := L) (p := p) : ℝ) := by
  unfold localDifferentPaperOrder
  rw [localDifferentOrder_eq_count]

#print axioms localDifferentOrder_eq_count
#print axioms localDifferentPaperOrder_eq_count

end LeanFormal.IUT.XiFPaper.Mzk1LocalDifferentCountActual
end