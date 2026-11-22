/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import tmp.sheaf.xif.paper.Mzk1ABCEstimatesArithmeticQpilotActual
import Mathlib.Tactic

/-! # Mzk1LocalEstimateConsumerQpilotActual — LocalEstimate consumer + gap correspondence

A630 (qpilot lane): port/research note for LANA `Iut/Concrete/LocalEstimate.lean`
(IUT IV Steps (iv)-(vii): distinguished-prime capsule bound, non-distinguished 0,
archimedean `|I|·log(√2·π)`; consumed by Theorem 1.10).  Without importing the
uncompiled LANA module, the *interface-level* consumer on our bridge type is
provided, together with the correspondence of the two IUT IV estimates to our
Gap 1 / Gap 2 fields. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1LocalEstimateConsumerQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCEstimatesArithmeticQpilotActual
open MeasureTheory
open scoped ENNReal

universe u

/-- The region log-volume as the `LocalEstimate`/`localEstimate` value (IUT IV
Steps (v)-(vii)), at the interface level. -/
noncomputable def localEstimateOfRegion {X : Type u} (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X) (a b c : Nat) : Real :=
  (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal

/-- Correspondence with the comparison-data accessor region. -/
theorem localEstimateOfRegion_comparisonRegion {X : Type u}
    {W : IQHullLogVolumeInterface X} {epsilon : Real}
    (C : Cor312EpsilonArithmeticComparison W epsilon) (a b c : Nat) :
    localEstimateOfRegion W C.logShellPoint a b c =
      (W.logVolume (C.comparisonRegion a b c)).toReal :=
  rfl

/-- The IUT IV estimate correspondence: Gap 1 (height vs local estimate) and
Gap 2 (local estimate vs weight) are exactly the comparison-data fields. -/
structure LocalEstimateGapCorrespondence {X : Type u}
    (W : IQHullLogVolumeInterface X) (logShellPoint : Nat → Nat → Nat → X) : Prop where
  /-- IUT IV gap 1: height comparison with the local estimate. -/
  height_le_localEstimate : ∀ epsilon : Real, 0 < epsilon →
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) * localEstimateOfRegion W logShellPoint a b c
  /-- IUT IV gap 2: local-estimate comparison with weight + θ + D. -/
  localEstimate_le_weight : ∀ epsilon : Real, 0 < epsilon → ∃ D : Real,
    ∀ a b c : Nat, IsABCTriple a b c →
      localEstimateOfRegion W logShellPoint a b c ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (W.logVolume W.hull).toReal + D

/-- Consumer: from the two IUT IV estimate correspondences the absorbed height
estimate follows (same arithmetic as `height_le_absorbed`). -/
theorem height_le_of_localEstimate {X : Type u} {W : IQHullLogVolumeInterface X}
    {logShellPoint : Nat → Nat → Nat → X}
    (E : LocalEstimateGapCorrespondence W logShellPoint)
    {epsilon : Real} (hpos : 0 < epsilon) (h1 : epsilon ≤ 1) :
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + 3 * epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (1 + epsilon) * ((W.logVolume W.hull).toReal + D) := by
  obtain ⟨D, hD⟩ := E.localEstimate_le_weight epsilon hpos
  refine ⟨D, fun a b c habc => ?_⟩
  have hge1 := E.height_le_localEstimate epsilon hpos a b c habc
  have hge2 := hD a b c habc
  have hw : (0 : Real) ≤ arithmeticWeight (abcRationalPoint a c) :=
    arithmeticWeight_nonneg _
  exact height_le_absorbed (le_of_lt hpos) h1 hw
    (height_le_of_twoEstimates (le_of_lt hpos) hge1 hge2)

/-- Consumer: from the two estimates, the `(1+3ε)` height bound with `D` (Gap
correspondence summary). -/
theorem localEstimate_gap_correspondence {X : Type u} {W : IQHullLogVolumeInterface X}
    {logShellPoint : Nat → Nat → Nat → X}
    (E : LocalEstimateGapCorrespondence W logShellPoint) :
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + 3 * (1 : Real)) * arithmeticWeight (abcRationalPoint a c) +
          (1 + (1 : Real)) * ((W.logVolume W.hull).toReal + D) :=
  height_le_of_localEstimate E (by norm_num) (by norm_num)

#check localEstimateOfRegion
#check localEstimate_gap_correspondence

end LeanFormal.IUT.XiFPaper.Mzk1LocalEstimateConsumerQpilotActual
end
