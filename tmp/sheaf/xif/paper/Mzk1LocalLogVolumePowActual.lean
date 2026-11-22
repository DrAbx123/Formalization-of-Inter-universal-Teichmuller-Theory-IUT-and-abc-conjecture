import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldProductHull
import Mathlib.Tactic
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1LocalLogVolumePowActual — integer-power scaling of local log-volume

Genuine new consumer theorems: scaling the local-field product by a natural
power or an integer power of a unit multiplies the Haar-character log by the
exponent.  Derived from normalizedLogVolume_smul, map_pow/map_zpow and
Real.log_pow/Real.log_zpow.  No paper object is claimed; no closure;
gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1LocalLogVolumePowActual

open LeanFormal.IUT
open MeasureTheory
open scoped Pointwise

attribute [instance] Set.mulActionSet

universe u

variable {ι : Type*} [Finite ι] {K : ι → Type*} [∀ i, NormedField (K i)]
  [∀ i, ProperSpace (K i)]
  [MeasurableSpace ((i : ι) → K i)] [BorelSpace ((i : ι) → K i)]
  (μ : Measure ((i : ι) → K i)) [Measure.IsAddHaarMeasure μ]

theorem normalizedLogVolume_smul_pow (g : (i : ι) → (K i)ˣ) (n : ℕ)
    {S : Set ((i : ι) → K i)} (hpos : 0 < μ S) (hfin : μ S < ⊤) :
    LocalFieldProductHull.normalizedLogVolume μ ((g ^ n) • S) =
      (n : ℝ) * Real.log (distribHaarChar ((i : ι) → K i) g : ℝ) +
        LocalFieldProductHull.normalizedLogVolume μ S := by
  rw [LocalFieldProductHull.normalizedLogVolume_smul μ (g ^ n) hpos hfin]
  have hchar : (distribHaarChar ((i : ι) → K i) (g ^ n) : ℝ) =
      (distribHaarChar ((i : ι) → K i) g : ℝ) ^ n := by
    rw [map_pow]
    push_cast
    ring
  rw [hchar, Real.log_pow]
  ring

theorem normalizedLogVolume_smul_zpow (g : (i : ι) → (K i)ˣ) (n : ℤ)
    {S : Set ((i : ι) → K i)} (hpos : 0 < μ S) (hfin : μ S < ⊤) :
    LocalFieldProductHull.normalizedLogVolume μ ((g ^ n) • S) =
      (n : ℝ) * Real.log (distribHaarChar ((i : ι) → K i) g : ℝ) +
        LocalFieldProductHull.normalizedLogVolume μ S := by
  rw [LocalFieldProductHull.normalizedLogVolume_smul μ (g ^ n) hpos hfin]
  have hchar : (distribHaarChar ((i : ι) → K i) (g ^ n) : ℝ) =
      (distribHaarChar ((i : ι) → K i) g : ℝ) ^ n := by
    rw [map_zpow]
    push_cast
    ring
  rw [hchar, Real.log_zpow]
  ring

end LeanFormal.IUT.XiFPaper.Mzk1LocalLogVolumePowActual

end
