/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesShaActual

/-!
# A607 two-estimates GAP DECOMPOSITION (mainline)

The unique remaining ABC gap `ABCTwoEstimates` is decomposed into two separately
trackable named inputs:
* `HeightEstimate`: the literal height comparison (`-|log Theta| >= -|log q|` shape);
* `VolumeEstimate`: the main log-volume estimate (HDD/SHE shape);
with a shared log-volume functional.  This makes each IUT IV Thm 1.10 estimate an
explicit hypothesis record and lets consumers report which one is missing.

No object is changed; conditional only (ABC gate NOT passed). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesGapDecompositionActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesShaActual

/-- Gap 1: the literal height comparison estimate. -/
structure HeightEstimate where
  logVolume : Nat → Nat → Nat → Real
  hheight : ∀ δ : Real, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * logVolume a b c

/-- Gap 2: the main log-volume (HDD/SHE) estimate. -/
structure VolumeEstimate where
  logVolume : Nat → Nat → Nat → Real
  hullVolume : Real
  hmain : ∀ δ : Real, 0 < δ → ∃ D : Real,
    ∀ a b c : Nat, IsABCTriple a b c →
      logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
        hullVolume + D

/-- The two gap records, sharing the same log-volume functional. -/
structure TwoEstimatesPair where
  volume : Nat → Nat → Nat → Real
  height : HeightEstimate
  main : VolumeEstimate
  height_logVolume : height.logVolume = volume
  main_logVolume : main.logVolume = volume

/-- Combine a pair of gap records into `ABCTwoEstimates`. -/
def twoEstimatesOfPair (P : TwoEstimatesPair) : ABCTwoEstimates where
  logVolume := P.volume
  hullVolume := P.main.hullVolume
  height_estimate := by
    have h := P.height.hheight
    rw [P.height_logVolume] at h
    exact h
  volume_estimate := by
    have h := P.main.hmain
    rw [P.main_logVolume] at h
    exact h

/-- The two estimates imply ABC through the decomposed pair. -/
theorem abc_of_pair (P : TwoEstimatesPair) : ABCConjecture :=
  abc_of_twoEstimates (twoEstimatesOfPair P)

/-- The height gap part of `ABCTwoEstimates`. -/
def heightOfTwoEstimates (E : ABCTwoEstimates) : HeightEstimate where
  logVolume := E.logVolume
  hheight := E.height_estimate

/-- The volume gap part of `ABCTwoEstimates`. -/
def mainOfTwoEstimates (E : ABCTwoEstimates) : VolumeEstimate where
  logVolume := E.logVolume
  hullVolume := E.hullVolume
  hmain := E.volume_estimate

/-- Every `ABCTwoEstimates` decomposes into a pair. -/
def pairOfTwoEstimates (E : ABCTwoEstimates) : TwoEstimatesPair where
  volume := E.logVolume
  height := heightOfTwoEstimates E
  main := mainOfTwoEstimates E
  height_logVolume := rfl
  main_logVolume := rfl

/-- The unique remaining gap is exactly a pair of the two named estimates. -/
theorem nonempty_pair_iff :
    Nonempty ABCTwoEstimates ↔ Nonempty TwoEstimatesPair :=
  ⟨fun ⟨E⟩ => ⟨pairOfTwoEstimates E⟩, fun ⟨P⟩ => ⟨twoEstimatesOfPair P⟩⟩

end LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesGapDecompositionActual

end
