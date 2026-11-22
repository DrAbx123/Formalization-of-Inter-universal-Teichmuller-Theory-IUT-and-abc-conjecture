import tmp.sheaf.xif.paper.PaperLevelXiFTargetActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual

/-! # Bridge from the proof-local xi-f scalars to the paper target

This file identifies the proof-local normalized q/Theta scalars with the
target scalars and derives `ActualPaperXiFTarget`. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

theorem globalQPilotLog_eq_neg_actualMagnitude :
    globalQPilotLog (l := l) T =
      -actualQPilotMagnitudeClassical (l := l) T := by
  unfold actualQPilotMagnitudeClassical globalQPilotLog perBQPilotLog
  trace_state
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [qPilotNormLog_eq (l := l) T b (Measure.addHaar)]
  simp [rootNormCoefficient, qVFamNormalizedCoefficientFamily, qVFamTensorV]

theorem actualQPilotSigned_eq_globalQPilotLog :
    actualQPilotSignedLogClassical (l := l) T =
      globalQPilotLog (l := l) T := by
  unfold actualQPilotSignedLogClassical
  rw [globalQPilotLog_eq_neg_actualMagnitude]

theorem actualThetaHullLogRoot_eq_globalThetaHullLog :
    actualThetaHullLogRoot (l := l) T =
      globalThetaHullLog (l := l) T := by
  unfold actualThetaHullLogRoot actualLocalHullLog globalThetaHullLog perBThetaHullLog
  simp only [actualLocalHullRegion, actualRootThetaHull, actualRootThetaImageSet,
    actualRootThetaRegion, actualRootCoeff, rootThetaHull, rootThetaImageSet,
    rootThetaRegion, rootHalfCoefficient, rootNormCoefficient]
  rfl

theorem actualPaperXiFTarget :
    ActualPaperXiFTarget (l := l) T := by
  unfold ActualPaperXiFTarget
  rw [actualQPilotSigned_eq_globalQPilotLog (l := l) T,
    actualThetaHullLogRoot_eq_globalThetaHullLog (l := l) T]
  exact globalQPilotLog_le_globalThetaHullLog (l := l) T

end LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetBridgeActual

end
