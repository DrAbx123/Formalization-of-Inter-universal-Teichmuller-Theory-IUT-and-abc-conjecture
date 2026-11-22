/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesShaActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-!
# A613 two-estimates MODEL-ONLY reduction (mainline; NOT paper Gap 2)

**MODEL-ONLY / ILLUSTRATIVE**: we instantiate the two-estimate record on the
canonical explicit model `arithmeticLogVolume a b c := arithmeticWeight (abcRationalPoint a c)`.
On THIS MODEL the volume slot holds trivially with `hullVolume = 0`, `D = 0`
(nonnegativity of the arithmetic weight).

**This is NOT the paper Gap 2.** The paper Gap 2 is a log-volume estimate on the
`normalizedComparisonRegion` / region log-volume (see the Sha lane's
`Mzk1ABCTwoEstimatesRealModelShaActual`), not on `arithmeticWeight`.  Here Gap 2 is
only model-instantiated so that the remaining gap on this toy model is the single
named `HeightModelInput`; from it the ABC conjecture follows through the green
`abc_of_twoEstimates`.

No object is changed, no `sorry`/custom axiom; both the height input and the true
paper Gap 2 remain named. ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesRealModelActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesShaActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual

/-- Canonical explicit log-volume model (the arithmetic weight). -/
noncomputable def arithmeticLogVolume : Nat → Nat → Nat → Real :=
  fun a b c => arithmeticWeight (abcRationalPoint a c)

theorem arithmeticLogVolume_nonneg (a b c : Nat) :
    0 ≤ arithmeticLogVolume a b c :=
  LeanFormal.IUT.arithmeticWeight_nonneg (abcRationalPoint a c)

/-- **MODEL-ONLY** (NOT paper Gap 2): on the toy model `arithmeticLogVolume :=
  arithmeticWeight` the volume slot holds with `hullVolume = 0`, `D = 0`.  This
  does not prove the paper Gap 2 (region log-volume). -/
theorem volume_estimate_arithmeticModel :
    ∀ δ : Real, 0 < δ → ∃ D : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        arithmeticLogVolume a b c ≤
          (1 + δ) * arithmeticWeight (abcRationalPoint a c) + 0 + D := by
  intro δ hδ
  refine ⟨0, fun a b c _ => ?_⟩
  have hw : 0 ≤ arithmeticWeight (abcRationalPoint a c) := arithmeticLogVolume_nonneg a b c
  simp [arithmeticLogVolume]
  nlinarith [hw, hδ.le]

/-- The remaining HEIGHT comparison input on the canonical model. -/
structure HeightModelInput where
  hheight : ∀ δ : Real, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * arithmeticLogVolume a b c

/-- From the height input on the **toy** model, the two-estimate record exists.
  (The volume field is the model-only proof above.) -/
noncomputable def twoEstimatesOfHeightModel (H : HeightModelInput) : ABCTwoEstimates where
  logVolume := arithmeticLogVolume
  hullVolume := 0
  height_estimate := H.hheight
  volume_estimate := volume_estimate_arithmeticModel

/-- **ABC from the single height input on the toy model** (model-only reduction;
  NOT a proof of the paper Gap 2). -/
theorem abc_of_heightModel (H : HeightModelInput) : ABCConjecture :=
  abc_of_twoEstimates (twoEstimatesOfHeightModel H)

end LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesRealModelActual

end
/-! ### Axiom gate (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesRealModelActual.abc_of_heightModel
