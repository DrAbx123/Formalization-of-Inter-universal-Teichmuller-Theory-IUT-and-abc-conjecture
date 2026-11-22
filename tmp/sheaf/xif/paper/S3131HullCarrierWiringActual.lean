import tmp.sheaf.xif.paper.S3132HullReadoutForBatchAActual
import tmp.sheaf.xif.paper.S3132IQHullRealLogVolumeReadoutActual
import tmp.sheaf.xif.paper.S3131QCActualReadout

/-! # S3131: wiring hull's actual H_C layer to the S3131 q readout

Consumes hull stream's citable H_C layer directly (no re-wrapping):
* S3129IQHullLogVolumeSourceActual: actual source Q_l log-shell image, actual
  Haar normalized to mass one on the integral log-shell, hull log-volume finite
  as a theorem;
* S3132IQHullRealLogVolumeReadoutActual: sourceHullRealLogVolume, the real Haar
  log-volume readout of the actual source hull;
* S3132HullReadoutForBatchAActual: sourceQCLeHCData, the S3130QCLeHCData on
  concreteLogShellField with W = sourceIQHullLogVolume and arbitrary qReadout,
  plus sourceQCLeHCData_HC / _QC / _HC_finite and the image-bound reduction
  sourceQCLeHCData_gap_of_image_bound.

Here qReadout is the S3131 same-C native q-side scalar S3131QC T
(nativeQVPilotNormalizedSignedLogVolume T).  The resulting Batch A comparison
target is exactly `S3131QC T <= H_C` in the existing S3130QCLeHCGap shape:
S3131WiredTarget_iff.  It is NOT proved here.

Readout forms are kept distinct and explicit: H_C here is the actual source
Haar log-volume (sourceHullRealLogVolume) on the concrete Example 3.6 Q_5
carrier; the q readout is the degree-normalized signed qVFamily scalar.  No
identification of the two readout forms and no same-C model identification are
asserted (cf. S3134SameCBridgeActual for the native-contract bridge, and lattice
S3137QThetaPilotLogVolumeReadingsActual for the Stage-2 C3 readings).
No sorry/axiom/True/PUnit.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3131HullCarrierWiringActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual
open LeanFormal.IUT.XiFPaper.S3132IQHullRealLogVolumeReadoutActual
open LeanFormal.IUT.XiFPaper.S3132HullReadoutForBatchAActual
open LeanFormal.IUT.XiFPaper.S3130QCLeHCActual
open LeanFormal.IUT.XiFPaper.S3131QCActualReadout

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The Batch A data package on hull's actual source H_C carrier, with the
S3131 native q-side readout as qReadout. -/
noncomputable def S3131BatchAOnSourceCarrier :
    S3130QCLeHCData concreteLogShellField :=
  sourceQCLeHCData (S3131QC T)

/-- The q readout of the wired package is the S3131 native q side. -/
theorem S3131BatchAOnSourceCarrier_QC :
    (S3131BatchAOnSourceCarrier T).QC = S3131QC T :=
  sourceQCLeHCData_QC (S3131QC T)

/-- H_C of the wired package is hull's actual real Haar hull readout. -/
theorem S3131BatchAOnSourceCarrier_HC :
    (S3131BatchAOnSourceCarrier T).HC = sourceHullRealLogVolume :=
  sourceQCLeHCData_HC (S3131QC T)

/-- Finiteness of the wired H_C (actual theorem of the S3129/S3132 layer). -/
theorem S3131BatchAOnSourceCarrier_HC_finite :
    (S3131BatchAOnSourceCarrier T).W.logVolume
        (S3131BatchAOnSourceCarrier T).W.hull < ⊤ :=
  sourceQCLeHCData_HC_finite (S3131QC T)

/-- The wired Batch A target is exactly the S3130QCLeHCGap, i.e.
`S3131QC T <= sourceHullRealLogVolume`. -/
theorem S3131WiredTarget_iff :
    S3130QCLeHCGap (S3131BatchAOnSourceCarrier T) ↔
      S3131QC T ≤ sourceHullRealLogVolume := by
  unfold S3130QCLeHCGap
  rw [S3131BatchAOnSourceCarrier_QC T, S3131BatchAOnSourceCarrier_HC T]

/-- The named Batch A target on hull's actual H_C carrier (not proved). -/
def S3131WiredTarget : Prop := S3130QCLeHCGap (S3131BatchAOnSourceCarrier T)

/-- Reduction of the wired target to hull's image-union bound: if the native q
readout is at most the actual source image Haar log-volume then the wired
target holds, by hull's actual sourceQCLeHCData_gap_of_image_bound. -/
theorem S3131WiredTarget_of_image_bound
    (h : S3131QC T ≤
      ((sourceIQHullLogVolume).logVolume
        (sourceIQHullLogVolume).imageSet).toReal) :
    S3131WiredTarget T := by
  unfold S3131WiredTarget
  exact sourceQCLeHCData_gap_of_image_bound (S3131QC T) h

#check S3131BatchAOnSourceCarrier
#check S3131WiredTarget_iff
#check S3131WiredTarget_of_image_bound
#check S3131BatchAOnSourceCarrier_HC

end LeanFormal.IUT.XiFPaper.S3131HullCarrierWiringActual

end
