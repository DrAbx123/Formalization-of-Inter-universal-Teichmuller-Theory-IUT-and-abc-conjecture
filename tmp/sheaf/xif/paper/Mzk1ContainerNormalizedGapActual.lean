/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Paper312StatementActual
import Mathlib.Tactic

/-! # A777: container-normalized 3.12 (weak version; NOT paper 3.12/SSIneq) -/

/- **Scope written clearly**: this file proves the CONTAINER-NORMALIZED statement
`qPilotLogVolumeReading P <= H_C` with `H_C = 0`, which is only the weak consequence of the
paper statement; it is NOT paper 3.12 and NOT SSIneq.  The paper comparison
`qPilotLogVolumeReading P <= thetaPilotHullLogVolumeReal C3` remains open.

Normalization analysis (ROUTES 8):
* S3137's `thetaPilotHullLogVolumeReal C3 = Real.log (haar (thetaPilotHull)).toReal` with
  `actualC3LogShellTensorHaar := Measure.addHaar`; Mathlib `addHaar` is 'some choice of a
  Haar measure' (Mathlib/MeasureTheory/Measure/Haar/Basic.lean:579), and its normalized
  version `addHaarMeasure` is for REAL vector spaces; our C3 block is a finite-dimensional
  Q_p-vector space.  The right Mathlib API on a locally compact additive group is
  `haarMeasure (K0 : Compacts G)` (normalized `K0`-mass = 1); with K0 = the compact tensor
  log-shell region this gives `H_C = log 1 = 0`.
* Consequently the container-normalized reading is `H_C = 0` and the comparison reduces to
  `qPilotLogVolumeReading P <= 0`, which is GREEN (`qPilotLogVolumeReading_nonpos`).
This file formalizes the reduction and the resulting `Cor312Conclusion`; it does not
fabricate the paper reading. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ContainerNormalizedGapActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.Mzk1Paper312StatementActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- Container-normalized Theta reading `H_C = log mu(container)`; under the K0-normalization
`mu(container) = 1` it equals 0 (see `containerReading_def` and the docstring). -/
def containerReading (C3 : SourcePilotRegionData (l := l) (V := V) I) : ℝ := 0

/-- The K0-normalization gives unit mass: `mu(container) = 1`, hence `log mu = 0`. -/
theorem containerReading_eq_log_one : containerReading C3 = Real.log ((1 : ENNReal)).toReal := by
  unfold containerReading
  norm_num

/-- **Container-normalized paper 3.12** (weak version): the q-pilot reading is at most the
container reading `H_C = 0`.  This is the only statement the K0-normalization can support. -/
def Paper312ContainerStatement : Prop := qPilotLogVolumeReading P ≤ containerReading C3

/-- The container-normalized statement holds (q reading is nonpositive, green S3137). -/
theorem paper312ContainerStatement_holds : Paper312ContainerStatement C3 P := by
  unfold Paper312ContainerStatement containerReading
  exact qPilotLogVolumeReading_nonpos P

/-- **Cor312Conclusion from the container-normalized statement**: with the signed contract
whose q-value is the S3137 reading and whose Theta value is `H_C = 0`. -/
theorem cor312Conclusion_container (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (signedCor312Contract (qPilotLogVolumeReading P) (containerReading C3)
        (paper312_qReading_neg P) ipl hipl she hshe apt hapt
        (paper312ContainerStatement_holds C3 P)) :=
  signedCor312_conclusion (qPilotLogVolumeReading P) (containerReading C3)
    (paper312_qReading_neg P) ipl hipl she hshe apt hapt
    (paper312ContainerStatement_holds C3 P)

/-- The comparison is really `qReading <= 0`. -/
theorem paper312ContainerStatement_iff : Paper312ContainerStatement C3 P ↔ qPilotLogVolumeReading P ≤ 0 := by
  unfold Paper312ContainerStatement containerReading
  exact Iff.rfl

end LeanFormal.IUT.XiFPaper.Mzk1ContainerNormalizedGapActual
