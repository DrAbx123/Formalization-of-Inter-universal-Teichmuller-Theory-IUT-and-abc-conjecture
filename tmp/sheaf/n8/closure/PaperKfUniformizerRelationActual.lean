import tmp.sheaf.n8.closure.PaperKfDVRGeneric
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellRamificationInertia

set_option maxHeartbeats 4000000
set_option relaxedAutoImplicit false

/-!
# PaperKf uniformizer relation: actual norm inequalities

Actual p-unit and irreducible-uniformizer norm inequalities.  The remaining
positive-exponent relation is reduced to a precise positivity lemma; no
arbitrary uniformizer and no native X.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.PaperKfUniformizerRelationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.PaperKfDVRGeneric

open MeasureTheory
open scoped BigOperators ENNReal TensorProduct Pointwise NNReal

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev PaperKf : Type := CommonPrimeCompletion (placeAtPrime S)

theorem paperPrimeUnit_norm_lt_one :
    ‖(PaperKfHaarNormActual.paperPrimeUnit S : PaperKf S)‖ < 1 := by
  change ‖(pNat S : ℚ_[pNat S]) • (1 : PaperKf S)‖ < 1
  rw [norm_smul, norm_one, mul_one]
  exact Padic.norm_p_lt_one (p := pNat S)

/-- The chosen irreducible uniformizer has norm strictly below one. -/
theorem paperUniformizer_norm_lt_one :
    ‖((paperUniformizer S : Integers (PaperKf S)) : PaperKf S)‖ < 1 := by
  have hle : ‖((paperUniformizer S : Integers (PaperKf S)) : PaperKf S)‖ ≤ 1 :=
    (mem_integers_iff _).mp (paperUniformizer S).property
  have hne : ‖((paperUniformizer S : Integers (PaperKf S)) : PaperKf S)‖ ≠ 1 := by
    intro hnorm
    have hmem_inv : (((paperUniformizer S : Integers (PaperKf S)) : PaperKf S))⁻¹ ∈
        Integers (PaperKf S) := by
      rw [mem_integers_iff, norm_inv, hnorm]
      norm_num
    let inv : Integers (PaperKf S) :=
      ⟨(((paperUniformizer S : Integers (PaperKf S)) : PaperKf S))⁻¹, hmem_inv⟩
    have hunit : IsUnit (paperUniformizer S) := by
      rw [isUnit_iff_exists_inv]
      refine ⟨inv, ?_⟩
      apply Subtype.ext
      change ((paperUniformizer S : Integers (PaperKf S)) : PaperKf S) *
        (((paperUniformizer S : Integers (PaperKf S)) : PaperKf S))⁻¹ = 1
      exact mul_inv_cancel₀ (by
        intro hzero
        exact (paperUniformizer_irreducible S).ne_zero (Subtype.ext hzero))
    exact (paperUniformizer_irreducible S).not_isUnit hunit
  exact lt_of_le_of_ne hle hne

/-- Exact positivity target left after the actual decomposition
pUnit = u * pi^z: the DVR exponent z is strictly positive. -/
def MissingPositiveUniformizerExponent : Prop :=
  ∀ (q : (PaperKf S)ˣ),
    q = PaperKfHaarNormActual.paperPrimeUnit S →
    ∀ (z : ℤ) (u : (PaperKf S)ˣ),
      q = u * PaperKfDVRGeneric.paperUniformizerUnit S ^ z →
      u • (Integers (PaperKf S) : Set (PaperKf S)) =
        (Integers (PaperKf S) : Set (PaperKf S)) →
      ‖(u : PaperKf S)‖ = 1 →
      0 < z

/-- The DVR exponent of pUnit with respect to the chosen uniformizer is positive. -/
theorem missingPositiveUniformizerExponent_actual :
    MissingPositiveUniformizerExponent S := by
  intro q hq z u hzu _huO hunorm
  rw [hq] at hzu
  have hπpos : 0 < ‖(PaperKfDVRGeneric.paperUniformizerUnit S : PaperKf S)‖ := by
    exact norm_pos_iff.mpr (Units.ne_zero (PaperKfDVRGeneric.paperUniformizerUnit S))
  have hπlt : ‖(PaperKfDVRGeneric.paperUniformizerUnit S : PaperKf S)‖ < 1 := by
    simpa [PaperKfDVRGeneric.paperUniformizerUnit] using paperUniformizer_norm_lt_one S
  have hnorm_eq : ‖(PaperKfHaarNormActual.paperPrimeUnit S : PaperKf S)‖ =
      ‖(PaperKfDVRGeneric.paperUniformizerUnit S : PaperKf S)‖ ^ z := by
    rw [hzu, Units.val_mul, Units.val_zpow_eq_zpow_val]
    rw [norm_mul, hunorm, one_mul, norm_zpow]
  by_contra hz
  have hzle : z ≤ 0 := le_of_not_gt hz
  have hone : 1 ≤ ‖(PaperKfDVRGeneric.paperUniformizerUnit S : PaperKf S)‖ ^ z :=
    one_le_zpow_of_nonpos₀ hπpos (le_of_lt hπlt) hzle
  have hPge : 1 ≤ ‖(PaperKfHaarNormActual.paperPrimeUnit S : PaperKf S)‖ := by
    rw [hnorm_eq]
    exact hone
  exact (not_le_of_gt (paperPrimeUnit_norm_lt_one S)) hPge

end LeanFormal.IUT.N8Closure.PaperKfUniformizerRelationActual

end