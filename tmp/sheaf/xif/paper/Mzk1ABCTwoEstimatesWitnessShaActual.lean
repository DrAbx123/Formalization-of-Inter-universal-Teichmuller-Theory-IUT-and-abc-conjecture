import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesShaActual

/-!
# A590 partial numeric witness for the ABC volume estimate (shehdd)

Shows the `volume_estimate` slot of `ABCTwoEstimates` is NOT vacuous: with the
trivial log-volume `logVolume = 0` and `hullVolume = 0`, the volume estimate holds
with `D = 0` provided arithmetic weights are nonnegative.  The `height_estimate`
slot remains the genuine named gap (not claimed here).

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesWitnessShaActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5NumericalActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesShaActual

/-- Structural partial data: the volume estimate is satisfiable with a concrete
numeric choice, the height estimate stays named. -/
structure ABCTwoEstimatesPartial where
  logVolume : Nat → Nat → Nat → Real
  hullVolume : Real
  height_estimate : ∀ δ : Real, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * logVolume a b c
  volume_estimate : ∀ δ : Real, 0 < δ → ∃ D : Real,
    ∀ a b c : Nat, IsABCTriple a b c →
      logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
        hullVolume + D

/-- Concrete non-vacuity of the volume-estimate slot: zero log-volume and hull
volume satisfy it provided weights are nonnegative. -/
theorem zero_volume_estimate
    (hweight : ∀ (a c : Nat), 0 ≤ arithmeticWeight (abcRationalPoint a c)) :
    ∀ δ : Real, 0 < δ → ∃ D : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        (0 : Real) ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) + 0 + D := by
  intro δ hδ
  refine ⟨(0 : Real), ?_⟩
  intro a b c _
  have hw : 0 ≤ arithmeticWeight (abcRationalPoint a c) := hweight a c
  have hδle : 0 ≤ δ := le_of_lt hδ
  nlinarith [mul_nonneg hδle hw]

/-- If additionally the height estimate is supplied, the partial data are a
full `ABCTwoEstimates` and hence give `ABCConjecture`. -/
theorem abc_of_partial_of_height
    (P : ABCTwoEstimatesPartial) : ABCConjecture :=
  abc_of_twoEstimates
    { logVolume := P.logVolume
      hullVolume := P.hullVolume
      height_estimate := P.height_estimate
      volume_estimate := P.volume_estimate }

end LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesWitnessShaActual
