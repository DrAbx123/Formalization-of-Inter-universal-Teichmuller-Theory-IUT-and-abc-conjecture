import tmp.sheaf.xif.paper.S957TensorClosureContainmentActual
import tmp.sheaf.xif.paper.S956TensorPacketLogVolumeExactActual
import tmp.sheaf.xif.paper.S919GlobalWeightedInequalityActual

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S962TensorPacketPaperInequalityActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedThetaIndHullActual
open LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual
open LeanFormal.IUT.XiFPaper.S956TensorPacketLogVolumeExactActual
open LeanFormal.IUT.XiFPaper.S957TensorClosureContainmentActual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Normalized tensor-packet log-volume on FinalLValuedCarrier. -/
noncomputable def tensorNormalizedLogVolume
    (D : FinalLTensorLogVolumeData (l := l) T b)
    (S : Set (FinalLValuedCarrier T b)) : Real :=
  Real.log (D.measure S).toReal -
    Real.log (D.measure D.unitRegion).toReal

/-- Monotonicity of the normalized log-volume on the tensor carrier. -/
theorem tensorNormalizedLogVolume_mono
    (D : FinalLTensorLogVolumeData (l := l) T b)
    {S U : Set (FinalLValuedCarrier T b)} (hSU : S ⊆ U)
    (hSpos : 0 < D.measure S)
    (hUfin : D.measure U < ⊤) :
    tensorNormalizedLogVolume (l := l) T b D S ≤
      tensorNormalizedLogVolume (l := l) T b D U := by
  unfold tensorNormalizedLogVolume
  have hle : D.measure S ≤ D.measure U := measure_mono hSU
  have hSfin : D.measure S < ⊤ := lt_of_le_of_lt hle hUfin
  have hSpos' : 0 < (D.measure S).toReal :=
    ENNReal.toReal_pos (ne_of_gt hSpos) (ne_of_lt hSfin)
  have hUpos : 0 < (D.measure U).toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le hSpos hle)) (ne_of_lt hUfin)
  have hlog : Real.log (D.measure S).toReal ≤
      Real.log (D.measure U).toReal :=
    Real.log_le_log hSpos' (ENNReal.toReal_mono (ne_of_lt hUfin) hle)
  linarith

/-- qPilot tensor-packet log. -/
noncomputable def qPilotTensorLog
    (D : FinalLTensorLogVolumeData (l := l) T b) : Real :=
  tensorNormalizedLogVolume (l := l) T b D
    (qPilotPaperImageInLValued (l := l) T b)

/-- Paper tensor hull log. -/
noncomputable def paperTensorHullLog
    (D : FinalLTensorLogVolumeData (l := l) T b) : Real :=
  tensorNormalizedLogVolume (l := l) T b D
    (paperTensorHull (l := l) T b D)

/-- Conditional tensor-packet inequality: density + positivity + finiteness. -/
theorem qPilotTensorLog_le_paperTensorHullLog
    (D : FinalLTensorLogVolumeData (l := l) T b)
    (hdensity : S957ThetaImageDenseInQPilot (l := l) T b D)
    (hpos : 0 < D.measure (qPilotPaperImageInLValued (l := l) T b))
    (hfin : D.measure (paperTensorHull (l := l) T b D) < ⊤) :
    qPilotTensorLog (l := l) T b D ≤ paperTensorHullLog (l := l) T b D :=
  tensorNormalizedLogVolume_mono (l := l) T b D hdensity hpos hfin

/-- Global weighted tensor-packet inequality. -/
noncomputable def tensorPacketPaperWeightedInequality
    (D : ∀ b : Bad (nativePlaceSelection T),
      FinalLTensorLogVolumeData (l := l) T b) : Prop :=
  weightedPaperV (l := l) T
      (fun b => qPilotTensorLog (l := l) T b (D b)) ≤
    weightedPaperV (l := l) T
      (fun b => paperTensorHullLog (l := l) T b (D b))

theorem tensorPacketPaperWeightedInequality_of_perB
    (D : ∀ b : Bad (nativePlaceSelection T),
      FinalLTensorLogVolumeData (l := l) T b)
    (hdensity : ∀ b : Bad (nativePlaceSelection T),
      S957ThetaImageDenseInQPilot (l := l) T b (D b))
    (hpos : ∀ b : Bad (nativePlaceSelection T),
      0 < (D b).measure (qPilotPaperImageInLValued (l := l) T b))
    (hfin : ∀ b : Bad (nativePlaceSelection T),
      (D b).measure (paperTensorHull (l := l) T b (D b)) < ⊤) :
    tensorPacketPaperWeightedInequality (l := l) T D := by
  unfold tensorPacketPaperWeightedInequality
  apply weightedPaperV_mono (l := l) T
  intro b
  exact qPilotTensorLog_le_paperTensorHullLog (l := l) T b (D b)
    (hdensity b) (hpos b) (hfin b)

end LeanFormal.IUT.XiFPaper.S962TensorPacketPaperInequalityActual

end
