/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ProcessionNormalizedHullVolumeActual
import tmp.sheaf.gogopex.Iut.Stage1.PilotComparison
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract

/-! # A526: normalized candidate => Gogopex Stage1Comparison/StepXI contract -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1NormalizedCandidateContractActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.Mzk1ProcessionNormalizedHullVolumeActual
open Iut.Stage1

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The Gogopex `Stage1Comparison` from the normalized candidate: magnitudes are the
negated signed readings (`q := -qPilotLogVolumeReading`, `theta := -normalizedHullVolume`). -/
def stage1ComparisonOfNormCandidate {P : PaperQPilotObjectActual (l := l) (I := I)}
    (ref : Set (C3LogShellTensorBlock C3))
    (hcmp : qThetaPilotLogVolumeComparisonNorm C3 P ref)
    (hqneg : qPilotLogVolumeReading P < 0) : Stage1Comparison where
  theta := { side := PilotSide.theta, value := -thetaPilotHullLogVolumeNorm C3 ref }
  q := { side := PilotSide.q, value := -qPilotLogVolumeReading P }
  theta_side := rfl
  q_side := rfl
  q_positive := by
    show 0 < -qPilotLogVolumeReading P
    linarith
  comparison := by
    show -(-thetaPilotHullLogVolumeNorm C3 ref) ≥ -(-qPilotLogVolumeReading P)
    unfold qThetaPilotLogVolumeComparisonNorm at hcmp
    linarith

/-- The normalized candidate yields `Corollary312Inequality`. -/
theorem corollary312Inequality_of_normCandidate
    {P : PaperQPilotObjectActual (l := l) (I := I)}
    (ref : Set (C3LogShellTensorBlock C3))
    (hcmp : qThetaPilotLogVolumeComparisonNorm C3 P ref)
    (hqneg : qPilotLogVolumeReading P < 0) :
    Corollary312Inequality
      { side := PilotSide.theta, value := -thetaPilotHullLogVolumeNorm C3 ref }
      { side := PilotSide.q, value := -qPilotLogVolumeReading P } :=
  (stage1ComparisonOfNormCandidate C3 ref hcmp hqneg).comparison

/-- The StepXI contract built from the normalized comparison (ordered slots from the
candidate, evidence supplied by the caller). -/
def normContract {P : PaperQPilotObjectActual (l := l) (I := I)}
    (ref : Set (C3LogShellTensorBlock C3))
    (hcmp : qThetaPilotLogVolumeComparisonNorm C3 P ref)
    (hqneg : qPilotLogVolumeReading P < 0)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) : StepXIContract where
  qSigned := -qPilotLogVolumeReading P
  thetaSigned := -thetaPilotHullLogVolumeNorm C3 ref
  targetSigned := -qPilotLogVolumeReading P
  q_negative := by
    show -qPilotLogVolumeReading P < 0
    linarith
  ipl := ipl
  she := she
  apt := apt
  ipl_evidence := hipl
  she_evidence := hshe
  apt_evidence := hapt
  q_le_target := le_rfl
  target_le_theta := by
    show -qPilotLogVolumeReading P ≤ -thetaPilotHullLogVolumeNorm C3 ref
    unfold qThetaPilotLogVolumeComparisonNorm at hcmp
    linarith

/-- Cor 3.12 ordered conclusion from the normalized candidate. -/
theorem cor312Conclusion_of_normCandidate {P : PaperQPilotObjectActual (l := l) (I := I)}
    (ref : Set (C3LogShellTensorBlock C3))
    (hcmp : qThetaPilotLogVolumeComparisonNorm C3 P ref)
    (hqneg : qPilotLogVolumeReading P < 0)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion := 
  cor312_of_constructed_stepXI _

end LeanFormal.IUT.XiFPaper.Mzk1NormalizedCandidateContractActual
