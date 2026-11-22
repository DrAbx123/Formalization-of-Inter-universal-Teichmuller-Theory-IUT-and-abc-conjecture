import tmp.sheaf.xif.paper.Mzk1P6HCor312SandwichActual
import tmp.sheaf.xif.paper.Mzk1P6HCor312SandwichChain
import tmp.sheaf.xif.paper.Mzk1P8ActualDisplayHeightActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.P6HCor312IntegrationActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P6HCor312SandwichActual
open LeanFormal.IUT.XiFPaper.Mzk1P6HCor312SandwichChain

/-- Actual P6 hCor312 integration data from the new sandwich A-D: the actual
theta data, pilot region, paper q-pilot object, and the P6 theta upper. -/
structure P6HCor312IntegrationData where
  l : PrimeGeFive
  T : SourceNativeInitialThetaData.{0} l
  [fintypeBad : Fintype (Bad (nativePlaceSelection T))]
  [measBad : ∀ b, MeasurableSpace (qVFamTensorBlock T b)]
  [borelBad : ∀ b, BorelSpace (qVFamTensorBlock T b)]
  V : Type
  I : OriginalInput l V
  C3 : SourcePilotRegionData (l := l) (V := V) I
  P : Mzk1ActualReadingTargetActual.PaperQPilotObjectActual (l := l) (I := I)
  hP6 : actualThetaHullLogRoot (l := l) T ≤ thetaPilotHullLogVolumeReal C3

attribute [instance] P6HCor312IntegrationData.fintypeBad
attribute [instance] P6HCor312IntegrationData.measBad
attribute [instance] P6HCor312IntegrationData.borelBad

/-- Actual sandwich conclusion integrated from the P6 data. -/
theorem p6HCor312Integration_sandwich
    (D : P6HCor312IntegrationData) :
    actualQPilotSignedLogClassical (l := D.l) D.T ≤
      thetaPilotHullLogVolumeReal D.C3 :=
  p6_sandwichChain_hCor312 D.T D.C3 D.P D.hP6

/-- Actual P8-chain compatibility wrapper: the sandwich gives the P6 Cor312
comparison used upstream. -/
theorem p6HCor312Integration_forP8 (D : P6HCor312IntegrationData) :
    actualQPilotSignedLogClassical (l := D.l) D.T ≤
      thetaPilotHullLogVolumeReal D.C3 :=
  p6HCor312Integration_sandwich D

end LeanFormal.IUT.XiFPaper.P6HCor312IntegrationActual
end
