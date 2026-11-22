/- P6 hCor312 sandwich: P5 gives -M ≤ H_theta and the P6 upper bound gives
H_theta ≤ H_target, hence the actual Cor 3.12 comparison -M ≤ H_target. -/
import tmp.sheaf.xif.paper.P6HThetaNormalizationActual
import tmp.sheaf.xif.paper.Mzk1ActualReadingTargetActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.P6HThetaNormalizationActual
open LeanFormal.IUT.XiFPaper.Mzk1ActualReadingTargetActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P6HCor312SandwichActual
universe u v
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable {V : Type} (I : OriginalInput l V)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))
/-- Actual Cor 3.12 sandwich: P5 middle arrow plus the P6 theta upper bound
on the same H_theta. -/
theorem p6_hCor312_sandwich
    (hP6 : actualThetaHullLogRoot (l := l) T ≤ thetaPilotHullLogVolumeReal C3) :
    actualQPilotSignedLogClassical (l := l) T ≤ thetaPilotHullLogVolumeReal C3 :=
  le_trans (actualTargetSigned_actual (l := l) T) hP6
#print axioms p6_hCor312_sandwich
end LeanFormal.IUT.XiFPaper.Mzk1P6HCor312SandwichActual
end