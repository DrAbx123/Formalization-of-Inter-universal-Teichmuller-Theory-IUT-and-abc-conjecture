import tmp.sheaf.xif.paper.S3130QCLeHCActual
import tmp.sheaf.xif.paper.S3132IQHullRealLogVolumeReadoutActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators NNReal ENNReal

namespace LeanFormal.IUT.XiFPaper.S3132HullReadoutForBatchAActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.XiFPaper.S3130QCLeHCActual
open LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual
open LeanFormal.IUT.XiFPaper.S3132IQHullRealLogVolumeReadoutActual

/-!
# The actual H_C readout in the Batch A data shape

Batch A fixes one admissible input `C` and needs the two readings on the same
`C`: the signed q readout `Q_C` and the hull log-volume `H_C`, then the
comparison `Q_C <= H_C`.  This file supplies the H_C side from the actual
construction:

* `sourceQCLeHCData qReadout` is the Batch A package
  `S3130QCLeHCData concreteLogShellField` whose ambient interface
  `W` is the actual source-faithful `IQHullLogVolumeInterface` of
  `S3129IQHullLogVolumeSourceActual`;
* `sourceQCLeHCData_HC` identifies `H_C` with the actual real Haar
  log-volume of the actual source hull (`sourceHullRealLogVolume`);
* `sourceQCLeHCData_HC_finite` is the actual finiteness;
* `sourceQCLeHCData_gap_of_image_bound` **reduces the Batch A comparison
  `Q_C <= H_C` to the image-union lower bound**: if the signed q readout is at
  most the real image log-volume, then `Q_C <= H_C` holds, because the actual
  hull contains the actual image and the actual Haar measure is monotone.

The q readout `qReadout` is a parameter here exactly as in
`S3130QCLeHCData`; its paper q-mark provenance (the q-pilot zero-locus
identification) is a separate source obligation owned by the q-side stream, and
is not asserted.
-/

/-- The Batch A data package on the fixed actual carrier
`concreteLogShellField`, with the actual source-faithful IQ hull/log-volume
interface as ambient hull data.  The signed q readout is the explicit parameter
whose source provenance is a separate obligation. -/
noncomputable def sourceQCLeHCData (qReadout : ℝ) :
    S3130QCLeHCData concreteLogShellField where
  W := sourceIQHullLogVolume
  qReadout := qReadout

/-- The H_C readout of the Batch A package is the actual real Haar log-volume of
the actual source hull. -/
theorem sourceQCLeHCData_HC (qReadout : ℝ) :
    (sourceQCLeHCData qReadout).HC = sourceHullRealLogVolume := rfl

/-- The Q_C readout of the Batch A package is the supplied signed q readout. -/
theorem sourceQCLeHCData_QC (qReadout : ℝ) :
    (sourceQCLeHCData qReadout).QC = qReadout := rfl

/-- The H_C log-volume in the Batch A package is the actual hull log-volume. -/
theorem sourceQCLeHCData_HC_logVolume (qReadout : ℝ) :
    (sourceQCLeHCData qReadout).W.logVolume (sourceQCLeHCData qReadout).W.hull =
      ENNReal.ofReal sourceHullRealLogVolume :=
  sourceIQHull_logVolume_eq_ofReal

/-- **Actual finiteness of H_C in the Batch A shape.** -/
theorem sourceQCLeHCData_HC_finite (qReadout : ℝ) :
    (sourceQCLeHCData qReadout).W.logVolume (sourceQCLeHCData qReadout).W.hull < ⊤ :=
  (sourceQCLeHCData qReadout).HC_finite

/-- **Batch A comparison reduced to the image-union lower bound.**  If the signed
q readout is at most the real log-volume of the actual source image union, then
the Batch A gap `Q_C <= H_C` holds for the actual H_C readout, because the
actual hull contains the actual image and the actual Haar measure is monotone. -/
theorem sourceQCLeHCData_gap_of_image_bound (qReadout : ℝ)
    (h : qReadout ≤
      ((sourceIQHullLogVolume).logVolume
        (sourceIQHullLogVolume).imageSet).toReal) :
    S3130QCLeHCGap (sourceQCLeHCData qReadout) := by
  have hmono : ((sourceIQHullLogVolume).logVolume
        (sourceIQHullLogVolume).imageSet).toReal ≤
      sourceHullRealLogVolume :=
    sourceHullRealLogVolume_ge_image_toReal
  unfold S3130QCLeHCGap S3130QCLeHCData.QC S3130QCLeHCData.HC
  change qReadout ≤
    ((sourceQCLeHCData qReadout).W.logVolume (sourceQCLeHCData qReadout).W.hull).toReal
  rw [sourceQCLeHCData_HC_logVolume]
  rw [ENNReal.toReal_ofReal sourceHullRealLogVolume_nonneg]
  exact le_trans h hmono

/-- **Nonempty Batch A package with the actual H_C readout.**  For every signed q
readout there is a Batch A data package on the actual carrier whose H_C is the
actual real Haar log-volume of the actual source hull and is finite. -/
theorem exists_sourceQCLeHCData_with_actualHC (qReadout : ℝ) :
    ∃ D : S3130QCLeHCData concreteLogShellField,
      D.HC = sourceHullRealLogVolume ∧
        D.W.logVolume D.W.hull < ⊤ :=
  ⟨sourceQCLeHCData qReadout, sourceQCLeHCData_HC qReadout,
    sourceQCLeHCData_HC_finite qReadout⟩

#check sourceQCLeHCData
#check sourceQCLeHCData_HC
#check sourceQCLeHCData_HC_finite
#check sourceQCLeHCData_gap_of_image_bound
#check exists_sourceQCLeHCData_with_actualHC

end LeanFormal.IUT.XiFPaper.S3132HullReadoutForBatchAActual

end