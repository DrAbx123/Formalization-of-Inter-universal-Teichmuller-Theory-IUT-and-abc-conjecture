/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.Mzk1ProcessionContributionNumericsActual
import Mathlib.Tactic

/-!
# Mzk1HullProcessionAverageActual — reduced comparison against the procession-average bound

A522: the paper Theta-pilot hull log-volume coefficient from the procession
arithmetic is `H_model = ((l*+1)/12) * m * log p`.  This file proves the
**reduced 3.12 inequality** in the model: the q-pilot reading
`-|log q| = log||q||` is `≤ 0`, while `H_model ≥ 0` for `p > 1`, hence
`qPilotLogVolumeReading ≤ H_model`; at l = 13, p = 11, m = 5 the bound is
`(35/12) log 11`.  This is the true arithmetic side of the comparison; the
actual S3137 hull normalization remains the named candidate.

No new axiom. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HullProcessionAverageActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open scoped BigOperators

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- The procession-average closed form of the Theta-pilot hull log-volume
model: `((l*+1)/12) * m * log p`. -/
noncomputable def hullProcessionAverage (m n : Nat) (p : Real) : Real :=
  ((n : Real) + 1) / 12 * (m : Real) * Real.log p

/-- The model hull bound is nonnegative for `p > 1`. -/
theorem hullProcessionAverage_nonneg {m n : Nat} {p : Real} (hp : 1 < p) :
    0 ≤ hullProcessionAverage m n p := by
  unfold hullProcessionAverage
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (le_of_lt hp)
  positivity

/-- Reduced 3.12 inequality in the procession model: the q-pilot reading is
nonpositive, hence at most the nonnegative hull bound `((l*+1)/12) m log p`. -/
theorem qPilotLogVolumeReading_le_hullProcessionAverage {m n : Nat} {p : Real}
    (hp : 1 < p) :
    qPilotLogVolumeReading P ≤ hullProcessionAverage m n p :=
  le_trans (qPilotLogVolumeReading_nonpos P) (hullProcessionAverage_nonneg hp)

/-- Concrete l = 13 (l* = 6), p = 11, m = 5: the reduced bound is `35/12 log 11`. -/
theorem qPilotLogVolumeReading_le_thirteen :
    qPilotLogVolumeReading P ≤ hullProcessionAverage 5 6 (11 : Real) :=
  qPilotLogVolumeReading_le_hullProcessionAverage (P := P) (by norm_num)

/-- The concrete bound equals `(35/12) log 11`. -/
theorem hullProcessionAverage_thirteen :
    hullProcessionAverage 5 6 (11 : Real) =
      (35 / 12) * Real.log (11 : Real) := by
  unfold hullProcessionAverage
  norm_num
  ring

/-- The concrete reduced inequality written with the explicit constant. -/
theorem qPilotLogVolumeReading_le_thirteen_explicit :
    qPilotLogVolumeReading P ≤ (35 / 12) * Real.log (11 : Real) :=
  (qPilotLogVolumeReading_le_thirteen P).trans_eq (hullProcessionAverage_thirteen)

#check qPilotLogVolumeReading_le_hullProcessionAverage
#check qPilotLogVolumeReading_le_thirteen_explicit

end LeanFormal.IUT.XiFPaper.Mzk1HullProcessionAverageActual
end
