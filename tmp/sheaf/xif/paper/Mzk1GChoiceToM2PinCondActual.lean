/- Light conditional pin data: normalized critical values from the raw inclusion.

`gPoly`'s raw critical values are {0, critFrac D}; the M2 pin needs {0,1} for
`gPolyNorm = C (critFrac D)^{-1} * gPoly D`.  This file proves the reduction
conditionally on the raw inclusion (which lives in the heavy
`Mzk1CritValueInImageFinalActual.gPoly_criticalValues_subset`, currently blocked by
infra); instantiate `hraw := gPoly_criticalValues_subset D` when it compiles.
Reuse: `Mzk1GChoiceScaleActual.critFrac`/`critFrac_ne_zero`, `Mzk1Lemma22GChoiceConstructActual.gPoly`.
-/
import tmp.sheaf.xif.paper.Mzk1GChoiceScaleActual
import tmp.sheaf.xif.paper.Mzk1Lemma22GChoiceConstructActual
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1GChoiceToM2PinCondActual

open LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceConstructActual
open Polynomial

/-- the normalized polynomial critFrac^{-1} * gPoly. -/
noncomputable def gPolyNorm (D : Mzk1ScaleData) : Polynomial ℚ :=
  Polynomial.C (critFrac D)⁻¹ * gPoly D

/-- PROVED (conditional on the raw critical-values inclusion): the normalized
polynomial has critical values in {0,1}. -/
theorem gPolyNorm_criticalValues_subset_of_raw (D : Mzk1ScaleData)
    (hraw : {v : ℂ | ∃ z : ℂ,
        Polynomial.aeval z (Polynomial.derivative (gPoly D)) = 0 ∧
        Polynomial.aeval z (gPoly D) = v} ⊆ ({0, ((critFrac D : ℚ) : ℂ)} : Set ℂ)) :
    {v : ℂ | ∃ z : ℂ,
        Polynomial.aeval z (Polynomial.derivative (gPolyNorm D)) = 0 ∧
        Polynomial.aeval z (gPolyNorm D) = v} ⊆ ({0, 1} : Set ℂ) := by
  rintro v ⟨z, hz, rfl⟩
  have hc : ((critFrac D : ℚ) : ℂ) ≠ 0 := by exact_mod_cast critFrac_ne_zero D
  unfold gPolyNorm at hz ⊢
  rw [Polynomial.derivative_C_mul] at hz
  simp only [map_mul, Polynomial.aeval_C] at hz ⊢
  have hz' : Polynomial.aeval z (Polynomial.derivative (gPoly D)) = 0 :=
    (mul_eq_zero.mp hz).resolve_left hc
  have hmem := hraw ⟨z, hz', rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem ⊢
  rcases hmem with h | h
  · left
    rw [h, mul_zero]
  · right
    rw [h, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

end LeanFormal.IUT.XiFPaper.Mzk1GChoiceToM2PinCondActual
end
