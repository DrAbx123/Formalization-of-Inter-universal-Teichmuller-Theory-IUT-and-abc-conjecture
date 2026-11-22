import tmp.sheaf.xif.paper.Mzk1ABCBridgeHeightRegionActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesShaActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesAuditCorrectionShaActual

/-!
# shehdd A612 real-model two estimates from Gap 1 + Gap 2 (Sha)

Honest real-model bridge: with `logVolume` = the paper region volume
`(W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal` and
`hullVolume` = `(W.logVolume W.hull).toReal`, the two genuine input packages
* `Dheight ε : HeightRegionGap1Data W logShellPoint ε` (IUT IV section 2
  `height_le_normalizedRegionVolume`), and
* `gap2 ε : ∃ D0, regionVolume ≤ (1+ε)*weight + hull + D0` (Gap 2),
give the *real* `ABCTwoEstimates` object (no `logVolume := arithmeticWeight`
substitution) and hence `ABCConjecture` through the green numerical reduction.

The two Gap packages are the standard named inputs; this file only performs the
honest wiring.  No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesRealModelShaActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5NumericalActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeHeightRegionActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesShaActual

universe u

variable {X : Type u} (W : IQHullLogVolumeInterface X)
variable (logShellPoint : Nat → Nat → Nat → X)

/-- The real paper region log-volume as a `Nat → Nat → Nat → Real`. -/
noncomputable def realRegionLogVolume : Nat → Nat → Nat → Real :=
  fun a b c => (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal

theorem realRegionLogVolume_apply (a b c : Nat) :
    realRegionLogVolume W logShellPoint a b c =
      (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal := rfl

/-- The real `ABCTwoEstimates` object: height slot from Gap 1 (same δ), volume
slot from Gap 2 (per-ε `D`), no model substitution. -/
noncomputable def realABCTwoEstimates
    (Gap1 : ∀ ε : Real, 0 < ε → HeightRegionGap1Data W logShellPoint ε)
    (Gap2 : ∀ ε : Real, 0 < ε → ∃ D0 : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal ≤
          (1 + ε) * arithmeticWeight (abcRationalPoint a c) +
            (W.logVolume W.hull).toReal + D0) : ABCTwoEstimates where
  logVolume := realRegionLogVolume W logShellPoint
  hullVolume := (W.logVolume W.hull).toReal
  height_estimate := by
    intro δ hδ a b c htriple
    exact (Gap1 δ hδ).height_le_normalizedRegionVolume a b c htriple
  volume_estimate := by
    intro δ hδ
    obtain ⟨D0, hD0⟩ := Gap2 δ hδ
    refine ⟨D0, ?_⟩
    intro a b c htriple
    simpa [realRegionLogVolume] using hD0 a b c htriple

/-- Conditional ABC from the two real Gap packages. -/
theorem abc_of_realGap1Gap2
    (Gap1 : ∀ ε : Real, 0 < ε → HeightRegionGap1Data W logShellPoint ε)
    (Gap2 : ∀ ε : Real, 0 < ε → ∃ D0 : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal ≤
          (1 + ε) * arithmeticWeight (abcRationalPoint a c) +
            (W.logVolume W.hull).toReal + D0) : ABCConjecture :=
  abc_of_twoEstimates (realABCTwoEstimates W logShellPoint Gap1 Gap2)

/-- Conditional additive height bound from the same real Gap packages. -/
theorem heightBound_of_realGap1Gap2
    (Gap1 : ∀ ε : Real, 0 < ε → HeightRegionGap1Data W logShellPoint ε)
    (Gap2 : ∀ ε : Real, 0 < ε → ∃ D0 : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal ≤
          (1 + ε) * arithmeticWeight (abcRationalPoint a c) +
            (W.logVolume W.hull).toReal + D0) : ABCFormAdditiveHeightBound :=
  heightBound_of_twoEstimates (realABCTwoEstimates W logShellPoint Gap1 Gap2)

end LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesRealModelShaActual
