/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ProcessionNormalizedHullVolumeActual
import Mathlib.Tactic

/-!
# Mzk1NormalizedComparisonArithmeticActual — normalized comparison as pure real inequality

A526: using the normalized S3137 comparison object
(`Mzk1ProcessionNormalizedHullVolumeActual`:
`thetaPilotHullLogVolumeNorm = log(haar hull/haar ref)/dim`, reference value 0),
we record:
* the normalized candidate is exactly the real inequality
  `qPilotLogVolume P ≤ thetaPilotHullLogVolumeNorm C3`;
* it follows from nonnegativity of the normalized hull volume (q side is ≤0);
* the reference-relative form via `thetaPilotHullLogVolumeNorm_mul_dim`.

The truth of the nonnegativity/hull side remains the named comparison; no axiom. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1NormalizedComparisonArithmeticActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1ProcessionNormalizedHullVolumeActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- The normalized candidate is the pure real inequality. -/
theorem qThetaComparisonNorm_iff_real :
    qThetaComparisonNorm C3 P ↔
      qPilotLogVolume C3 P ≤ thetaPilotHullLogVolumeNorm C3 := Iff.rfl

/-- If the normalized hull volume is nonnegative, the normalized comparison holds
(the q reading is `≤ 0`). -/
theorem qThetaComparisonNorm_of_hull_nonneg
    (h : 0 ≤ thetaPilotHullLogVolumeNorm C3) :
    qThetaComparisonNorm C3 P :=
  le_trans (qPilotLogVolume_nonpos C3 P) h

/-- Reference-relative form: the normalized hull volume times the block dimension
is the unnormalized hull reading minus the reference constant, so the normalized
candidate is the real inequality with that fixed constant. -/
theorem qThetaComparisonNorm_iff_referenceForm
    (hdim : (0 : Real) < (c3TensorBlockDimension C3 : Real)) :
    qThetaComparisonNorm C3 P ↔
      qPilotLogVolume C3 P * (c3TensorBlockDimension C3 : Real) ≤
        thetaPilotHullLogVolumeReal C3 -
          Real.log ((actualC3LogShellTensorHaar C3)
            (normalizationReference C3)).toReal := by
  rw [qThetaComparisonNorm_iff_real, ← thetaPilotHullLogVolumeNorm_mul_dim C3]
  constructor
  · intro h
    exact mul_le_mul_of_nonneg_right h (le_of_lt hdim)
  · intro h
    exact (mul_le_mul_right hdim).mp h

#check qThetaComparisonNorm_iff_real
#check qThetaComparisonNorm_of_hull_nonneg

end LeanFormal.IUT.XiFPaper.Mzk1NormalizedComparisonArithmeticActual
end
