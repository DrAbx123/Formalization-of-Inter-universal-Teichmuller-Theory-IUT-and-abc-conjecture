/- Adapter: pin data for henry's M2BranchPinObligation (light imports; no P1 layer).

Reuse: `Mzk1GChoiceDegreeActual.gPoly_natDegree_pos`, `Mzk1CritValueInImageFinalActual.
{gPoly_critValue_zero_or_critFrac, gPoly_criticalValues_subset, critFrac_ne_zero}`, and
`Mzk1GChoiceScaleActual.{critFrac}`.  The raw gPoly critical values are {0, critFrac D}
(NOT {0,1}); the normalized polynomial `gPolyNorm D = C (critFrac D)^{-1} * gPoly D` has
critical values in {0,1} (this is the pin input).  The P1 beta-avoiding row is re-exported
by part 1 (`Mzk1GChoiceToM2Actual.gChoice_avoids_adapter`).
-/
import tmp.sheaf.xif.paper.Mzk1GChoiceDegreeActual
import tmp.sheaf.xif.paper.Mzk1Lemma22GChoiceConstructActual
import tmp.sheaf.xif.paper.Mzk1CritValueInImageFinalActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1GChoiceToM2PinActual

open LeanFormal.IUT.XiFPaper.Mzk1GChoiceDegreeActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceConstructActual
open LeanFormal.IUT.XiFPaper.Mzk1CritValueInImageFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual
open Polynomial

/-- (1) gPoly has positive natDegree (0 < form). -/
theorem gPoly_natDegree_pos_adapter (D : Mzk1ScaleData) : 0 < (gPoly D).natDegree :=
  lt_of_lt_of_le zero_lt_one (gPoly_natDegree_pos D)

/-- (2) gPoly has nonzero derivative. -/
theorem gPoly_derivative_ne_zero_adapter (D : Mzk1ScaleData) :
    Polynomial.derivative (gPoly D) ≠ 0 := by
  rw [Polynomial.derivative_ne_zero]
  exact Nat.ne_of_gt (lt_of_lt_of_le zero_lt_one (gPoly_natDegree_pos D))

/-- (3a) CLOSEST TRUE raw form: gPoly's critical values lie in {0, critFrac D}. -/
theorem gPoly_criticalValues_subset_adapter (D : Mzk1ScaleData) :
    {v : ℂ | ∃ z : ℂ, Polynomial.aeval z (Polynomial.derivative (gPoly D)) = 0 ∧
        Polynomial.aeval z (gPoly D) = v} ⊆ ({0, ((critFrac D : ℚ) : ℂ)} : Set ℂ) :=
  gPoly_criticalValues_subset D

/-- the normalized polynomial critFrac^{-1} * gPoly. -/
noncomputable def gPolyNorm (D : Mzk1ScaleData) : Polynomial ℚ :=
  Polynomial.C (critFrac D)⁻¹ * gPoly D

/-- (3b) PROVED: the normalized polynomial has critical values in {0,1}. -/
theorem gPolyNorm_criticalValues_subset (D : Mzk1ScaleData) :
    {v : ℂ | ∃ z : ℂ, Polynomial.aeval z (Polynomial.derivative (gPolyNorm D)) = 0 ∧
        Polynomial.aeval z (gPolyNorm D) = v} ⊆ ({0, 1} : Set ℂ) := by
  rintro v ⟨z, hz, rfl⟩
  have hc : ((critFrac D : ℚ) : ℂ) ≠ 0 := by exact_mod_cast critFrac_ne_zero D
  unfold gPolyNorm at hz ⊢
  rw [Polynomial.derivative_C_mul] at hz
  rw [map_mul, Polynomial.aeval_C] at hz ⊢
  have hc0 : ((algebraMap ℚ ℂ) (critFrac D)⁻¹) ≠ 0 := by
    simp only [map_inv₀]
    exact inv_ne_zero (by simpa using hc)
  have hz' : Polynomial.aeval z (Polynomial.derivative (gPoly D)) = 0 :=
    (mul_eq_zero.mp hz).resolve_left hc0
  rcases gPoly_critValue_zero_or_critFrac D hz' with h | h
  · left
    rw [h, mul_zero]
  · right
    rw [h]
    have hc' : ((critFrac D : ℚ) : ℂ)⁻¹ * ((critFrac D : ℚ) : ℂ) = 1 :=
      inv_mul_cancel₀ hc
    simpa using hc'

/-- (5) PROVED: a zero branch value is a rational value (c = 0). -/
theorem gPoly_value_mem_rat (D : Mzk1ScaleData) {z : ℂ}
    (h : Polynomial.aeval z (gPoly D) = 0) :
    ∃ c : ℚ, Polynomial.aeval z (gPoly D) = algebraMap ℚ ℂ c :=
  ⟨0, by rw [h, map_zero]⟩

end LeanFormal.IUT.XiFPaper.Mzk1GChoiceToM2PinActual
end