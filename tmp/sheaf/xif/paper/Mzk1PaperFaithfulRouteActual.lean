/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1QPilotRouteBridgeActual

/-!
# A703 paper-faithful 3.12 -> ABC conditional shape (mainline)

`PaperFaithfulReadout T` collects the explicit data of the paper-faithful bridge:
the q-pilot scale data on an explicit region, the q-pilot radical bound, plus the
paper's negative-theta input as an OPAQUE Prop (recorded, not derived).

* `paperFaithful_3_12_to_ABC`: any readout yields `ABCConjecture`;
* `paperFaithful_gap1_and_ABC`: it also yields the Gap 1 height comparison;
* `paperFaithful_boundary_equiv`: the readout boundary is exactly the q-pilot radical
  input (difficulty unchanged; in the corrected d_b=1 instance it equals
  `NatRadicalWeightBound` by the green bridge file).

No canonical change; ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperFaithfulRouteActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotRouteBridgeActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Explicit data of the paper-faithful route. -/
structure PaperFaithfulReadout : Type where
  /-- The explicit comparison region used by the q-pilot construction. -/
  region : Nat → Nat → Nat → Set (S1902Carrier T)
  /-- The q-pilot scale data on that region. -/
  qPilot : QPilotScaleDataOn T region
  /-- The remaining q-pilot radical bound. -/
  boundary : qPilotRadicalBoundOn T region qPilot
  /-- The paper's negative-theta input, as an opaque Prop (recorded, not derived). -/
  hqneg : Prop
  hqneg_proof : hqneg

/-- **Paper-faithful 3.12 -> ABC**: a readout yields `ABCConjecture`. -/
theorem paperFaithful_3_12_to_ABC (R : PaperFaithfulReadout T) : ABCConjecture :=
  qPilotRadicalBoundOn_implies_ABC T R.region R.qPilot R.boundary

/-- The same readout also gives the Gap 1 height comparison. -/
theorem paperFaithful_gap1_and_ABC
    (R : PaperFaithfulReadout T) (ε : ℝ) (hε : 0 < ε) :
    (∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + ε) * (s1902LogVolume T (R.region a b c)).toReal) ∧
      ABCConjecture :=
  ⟨gap1_of_qPilotRouteOn T R.region R.qPilot ε hε, paperFaithful_3_12_to_ABC T R⟩

/-- The readout boundary is exactly the q-pilot radical input (no difficulty removed). -/
theorem paperFaithful_boundary_equiv :
    (∃ R : PaperFaithfulReadout T, True) ↔
      (∃ (region : Nat → Nat → Nat → Set (S1902Carrier T))
        (D : QPilotScaleDataOn T region), qPilotRadicalBoundOn T region D) := by
  constructor
  · rintro ⟨R, _⟩
    exact ⟨R.region, R.qPilot, R.boundary⟩
  · rintro ⟨region, D, hbound⟩
    refine ⟨?_, trivial⟩
    exact { region := region, qPilot := D, boundary := hbound, hqneg := True, hqneg_proof := trivial }

/-- Scope rows of the paper-faithful route. -/
def paperFaithfulRows : List (String × String) :=
  [ ("readout fields", "region + q-pilot data + radical bound + opaque hqneg"),
    ("3.12 -> ABC", "PROVED (paperFaithful_3_12_to_ABC)"),
    ("Gap 1", "PROVED (paperFaithful_gap1_and_ABC)"),
    ("boundary", "exactly the q-pilot radical input; equals NatRadicalWeightBound in d_b=1"),
    ("scope", "paper-faithful shape; difficulty unchanged; ABC gate NOT passed") ]

theorem paperFaithfulRows_length : paperFaithfulRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1PaperFaithfulRouteActual

end

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperFaithfulRouteActual.paperFaithful_3_12_to_ABC
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperFaithfulRouteActual.paperFaithful_gap1_and_ABC
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperFaithfulRouteActual.paperFaithfulRows_length