/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesShaActual
import tmp.sheaf.xif.paper.Mzk1ABCStage5EstimateGapsActual
import tmp.sheaf.xif.paper.Mzk1ABCStage5NumericWitnessActual

/-!
# A594 numeric evidence for the unique remaining gap (`ABCTwoEstimates`)

Intermediate lemmas (no change of the objects):
* `gapsOfTwoEstimates` / `twoEstimatesOfGaps` — the two gap representations are
  equivalent records of the same two named IUT IV Thm 1.10 estimates
  (`height_estimate`, `volume_estimate`);
* `nonempty_twoEstimates_iff_gaps` — the gap is exactly one datum;
* `abc_via_gaps` — the ABC conclusion through the gap record;
* concrete numeric evidence for the `δ`-step used by the reduction.

The two estimates themselves remain the unique named gap; ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesNumericEvidenceActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesShaActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCStage5EstimateGapsActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCStage5NumericWitnessActual

/-- The two-estimate record as the explicit gap record. -/
def gapsOfTwoEstimates (E : ABCTwoEstimates) : ABCStage5Gaps where
  logVolume := E.logVolume
  hullVolume := E.hullVolume
  hheight := E.height_estimate
  hmain := E.volume_estimate

/-- The explicit gap record as the two-estimate record. -/
def twoEstimatesOfGaps (G : ABCStage5Gaps) : ABCTwoEstimates where
  logVolume := G.logVolume
  hullVolume := G.hullVolume
  height_estimate := G.hheight
  volume_estimate := G.hmain

/-- The two records carry the same two fields. -/
theorem gapsOfTwoEstimates_fields (E : ABCTwoEstimates) :
    (gapsOfTwoEstimates E).logVolume = E.logVolume ∧
      (gapsOfTwoEstimates E).hullVolume = E.hullVolume :=
  ⟨rfl, rfl⟩

/-- The unique remaining gap is exactly one datum. -/
theorem nonempty_twoEstimates_iff_gaps :
    Nonempty ABCTwoEstimates ↔ Nonempty ABCStage5Gaps :=
  ⟨fun ⟨E⟩ => ⟨gapsOfTwoEstimates E⟩, fun ⟨G⟩ => ⟨twoEstimatesOfGaps G⟩⟩

/-- ABC from the two estimates, routed through the explicit gap record. -/
theorem abc_via_gaps (E : ABCTwoEstimates) : ABCConjecture :=
  abc_of_gaps (gapsOfTwoEstimates E)

/-- Concrete numeric witness for the `δ`-step: `ε = 1/2`, `δ = 1/8`. -/
theorem concrete_delta_witness :
    (1 + (1 / 8 : ℝ)) ^ 2 ≤ 1 + (1 / 2 : ℝ) := by
  norm_num

end LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesNumericEvidenceActual