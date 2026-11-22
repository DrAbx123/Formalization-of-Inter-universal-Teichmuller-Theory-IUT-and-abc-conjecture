import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldProductHull
import Mathlib.Tactic
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1LocalLogVolumeScalingActual — multiplicativity of local log-volume scaling

Genuine new consumer theorems for the local-field product log-volume layer
(IUT IV Prop 1.4-type local log-volume scaling):
* scaling by a product g*h adds both Haar-character logs;
* scaling by g⁻¹ subtracts the Haar-character log.
Both are derived from the tree theorem normalizedLogVolume_smul and the
multiplicativity of distribHaarChar.  No paper object is claimed; no closure;
gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1LocalLogVolumeScalingActual

open LeanFormal.IUT
open MeasureTheory
open scoped Pointwise

attribute [local instance] Set.mulActionSet

universe u

variable {ι : Type*} [Finite ι] {K : ι → Type*} [∀ i, NormedField (K i)]
  [∀ i, ProperSpace (K i)]
  [MeasurableSpace ((i : ι) → K i)] [BorelSpace ((i : ι) → K i)]
  (μ : Measure ((i : ι) → K i)) [Measure.IsAddHaarMeasure μ]

/-- Scaling by g*h adds the logarithms of both Haar characters. -/
theorem normalizedLogVolume_smul_mul (g h : (i : ι) → (K i)ˣ)
    {S : Set ((i : ι) → K i)} (hpos : 0 < μ S) (hfin : μ S < ⊤) :
    LocalFieldProductHull.normalizedLogVolume μ ((g * h) • S) =
      Real.log (distribHaarChar ((i : ι) → K i) g : ℝ) +
        Real.log (distribHaarChar ((i : ι) → K i) h : ℝ) +
          LocalFieldProductHull.normalizedLogVolume μ S := by
  rw [LocalFieldProductHull.normalizedLogVolume_smul μ (g * h) hpos hfin]
  have hgh : (distribHaarChar ((i : ι) → K i) (g * h) : ℝ) =
      (distribHaarChar ((i : ι) → K i) g : ℝ) *
        (distribHaarChar ((i : ι) → K i) h : ℝ) := by
    rw [map_mul]
    push_cast
    ring
  rw [hgh]
  have hg : (distribHaarChar ((i : ι) → K i) g : ℝ) ≠ 0 := by
    exact_mod_cast (distribHaarChar_pos (A := (i : ι) → K i) (g := g)).ne'
  have hh : (distribHaarChar ((i : ι) → K i) h : ℝ) ≠ 0 := by
    exact_mod_cast (distribHaarChar_pos (A := (i : ι) → K i) (g := h)).ne'
  rw [Real.log_mul hg hh]

/-- Scaling by g⁻¹ subtracts the logarithm of the Haar character. -/
theorem normalizedLogVolume_smul_inv (g : (i : ι) → (K i)ˣ)
    {S : Set ((i : ι) → K i)} (hpos : 0 < μ S) (hfin : μ S < ⊤) :
    LocalFieldProductHull.normalizedLogVolume μ (g⁻¹ • S) =
      -Real.log (distribHaarChar ((i : ι) → K i) g : ℝ) +
        LocalFieldProductHull.normalizedLogVolume μ S := by
  rw [LocalFieldProductHull.normalizedLogVolume_smul μ (g⁻¹) hpos hfin]
  have hchar : (distribHaarChar ((i : ι) → K i) (g⁻¹) : ℝ) =
      (distribHaarChar ((i : ι) → K i) g : ℝ)⁻¹ := by
    rw [map_inv]
    push_cast
    ring
  rw [hchar, Real.log_inv]

end LeanFormal.IUT.XiFPaper.Mzk1LocalLogVolumeScalingActual

end
