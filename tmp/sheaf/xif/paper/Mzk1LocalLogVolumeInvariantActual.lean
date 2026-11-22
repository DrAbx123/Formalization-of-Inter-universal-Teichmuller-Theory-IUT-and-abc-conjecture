import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldProductHull
import Mathlib.Tactic
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1LocalLogVolumeInvariantActual — scaling invariance for unit Haar character

Genuine consumer: scaling the local-field product by a unit whose distributive
Haar character is 1 leaves the normalized log-volume unchanged.
Reuses normalizedLogVolume_smul and distribHaarChar positivity.  No paper object
is claimed; no closure; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1LocalLogVolumeInvariantActual

open LeanFormal.IUT
open MeasureTheory
open scoped Pointwise

attribute [local instance] Set.mulActionSet

universe u

variable {ι : Type*} [Finite ι] {K : ι → Type*} [∀ i, NormedField (K i)]
  [∀ i, ProperSpace (K i)]
  [MeasurableSpace ((i : ι) → K i)] [BorelSpace ((i : ι) → K i)]
  (μ : Measure ((i : ι) → K i)) [Measure.IsAddHaarMeasure μ]

theorem normalizedLogVolume_smul_of_char_one (g : (i : ι) → (K i)ˣ)
    (hchar : distribHaarChar ((i : ι) → K i) g = 1)
    {S : Set ((i : ι) → K i)} (hpos : 0 < μ S) (hfin : μ S < ⊤) :
    LocalFieldProductHull.normalizedLogVolume μ (g • S) =
      LocalFieldProductHull.normalizedLogVolume μ S := by
  rw [LocalFieldProductHull.normalizedLogVolume_smul μ g hpos hfin, hchar]
  norm_num

theorem normalizedLogVolume_smul_one {S : Set ((i : ι) → K i)}
    (hpos : 0 < μ S) (hfin : μ S < ⊤) :
    LocalFieldProductHull.normalizedLogVolume μ ((1 : (i : ι) → (K i)ˣ) • S) =
      LocalFieldProductHull.normalizedLogVolume μ S := by
  rw [one_smul]

end LeanFormal.IUT.XiFPaper.Mzk1LocalLogVolumeInvariantActual

end
