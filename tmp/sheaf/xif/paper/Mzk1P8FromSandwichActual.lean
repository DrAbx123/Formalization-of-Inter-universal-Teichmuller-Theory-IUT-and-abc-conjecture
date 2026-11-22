import tmp.sheaf.xif.paper.Mzk1P6HCor312IntegrationActual
import tmp.sheaf.xif.paper.Mzk1P8UniformHeightActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P8UniformHeightActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P8FromSandwichActual
universe u v
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable {V : Type} (I : OriginalInput l V)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))
/-- P8 sandwich data: actual P6 hCor312 sandwich plus the P8 uniform height input. -/
structure P8FromSandwichData (hP6 : actualThetaHullLogRoot (l := l) T ≤
    thetaPilotHullLogVolumeReal C3) where
  hCor312 : actualQPilotSignedLogClassical (l := l) T ≤ thetaPilotHullLogVolumeReal C3
  uniform : P8UniformHeightBound
noncomputable def p8FromSandwichData
    (hP6 : actualThetaHullLogRoot (l := l) T ≤ thetaPilotHullLogVolumeReal C3)
    (h : P8UniformHeightBound) : P8FromSandwichData (l := l) T I C3 P hP6 where
  hCor312 := p6_hCor312_integration (l := l) T I C3 P hP6
  uniform := h
theorem p8_from_sandwich_abc
    (hP6 : actualThetaHullLogRoot (l := l) T ≤ thetaPilotHullLogVolumeReal C3)
    (h : P8UniformHeightBound) : ABCConjecture :=
  p8UniformHeight_consumer h
#print axioms p8_from_sandwich_abc
end LeanFormal.IUT.XiFPaper.Mzk1P8FromSandwichActual
end