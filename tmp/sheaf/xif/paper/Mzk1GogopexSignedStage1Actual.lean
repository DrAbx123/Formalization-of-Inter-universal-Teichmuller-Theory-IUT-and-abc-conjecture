import tmp.sheaf.xif.paper.Mzk1MonotoneSignedDirectionActual
import tmp.sheaf.gogopex.Iut.Stage1.CorollarySchema
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Signed Stage1/Gogopex assembly from qRegion ⊆ hull

Signed log-volume containment gives the paper inequality directly; this file
packages it as a Gogopex `Stage1Comparison` and its `Corollary312Inequality`.
Measure nonzero/finite premises are explicit. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1GogopexSignedStage1Actual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1MonotoneSignedDirectionActual
open Iut.Stage1
open MeasureTheory

variable {X : Type*} [MeasurableSpace X]
variable (mu : Measure X)
variable {qRegion hull : Set X}

theorem signed_le_of_subset (hsub : qRegion ⊆ hull)
    (hq : 0 < mu qRegion) (hh : mu hull ≠ ⊤) :
    signedLogVolume mu qRegion ≤ signedLogVolume mu hull :=
  signedLogVolume_mono mu hsub hq hh

def signedStage1Comparison (hsub : qRegion ⊆ hull)
    (hq : 0 < mu qRegion) (hh : mu hull ≠ ⊤)
    (hneg : signedLogVolume mu qRegion < 0) :
    Stage1Comparison :=
  stage1Comparison_of_signed_le
    (thetaSigned := signedLogVolume mu hull)
    (qSigned := signedLogVolume mu qRegion)
    (by linarith [hneg])
    (signed_le_of_subset mu hsub hq hh)

theorem signedStage1Comparison_corollary312 (hsub : qRegion ⊆ hull)
    (hq : 0 < mu qRegion) (hh : mu hull ≠ ⊤)
    (hneg : signedLogVolume mu qRegion < 0) :
    Corollary312Inequality
      (signedStage1Comparison mu hsub hq hh hneg).theta
      (signedStage1Comparison mu hsub hq hh hneg).q :=
  corollary312_from_stage1_comparison
    (signedStage1Comparison mu hsub hq hh hneg)

end LeanFormal.IUT.XiFPaper.Mzk1GogopexSignedStage1Actual

end
