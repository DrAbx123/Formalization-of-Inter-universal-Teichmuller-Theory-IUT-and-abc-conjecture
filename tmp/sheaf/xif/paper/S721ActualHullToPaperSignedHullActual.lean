import tmp.sheaf.xif.paper.S706ThetaPilotHullLogActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual
import tmp.sheaf.xif.PaperSignedHull

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S721ActualHullToPaperSignedHullActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S706ThetaPilotHullLogActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory
open scoped BigOperators

universe uX uLabel
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable {X : Type uX} {label : Type uLabel} [Fintype label]

noncomputable def paperSignedHullOfActualHullLog
    (A : IQHullLogVolumeInterface X)
    (procession : WeightedValues label)
    (finiteHull : FiniteHull label)
    (hmatches : ∀ i, procession.value i = finiteHull.volume i)
    (hweights : ∀ i, 0 <= procession.weight i)
    (havg : 0 <= procession.average)
    (havg_eq : procession.average = -perBThetaHullLog T b)
    (hnormalActual : A.logVolume A.hull = ENNReal.ofReal (-perBThetaHullLog T b)) :
    PaperSignedHull X label where
  ambient := A
  procession := procession
  hull := finiteHull
  weighted_matches_hull := hmatches
  weights_nonnegative := hweights
  average_nonneg := havg
  hull_logVolume_eq_average := by
    rw [havg_eq]
    exact hnormalActual

theorem paperSignedHullOfActualHullLog_signed_eq
    (A : IQHullLogVolumeInterface X)
    (procession : WeightedValues label)
    (finiteHull : FiniteHull label)
    (hmatches : ∀ i, procession.value i = finiteHull.volume i)
    (hweights : ∀ i, 0 <= procession.weight i)
    (havg : 0 <= procession.average)
    (havg_eq : procession.average = -perBThetaHullLog T b)
    (hnormalActual : A.logVolume A.hull = ENNReal.ofReal (-perBThetaHullLog T b)) :
    (paperSignedHullOfActualHullLog T b A procession finiteHull hmatches
      hweights havg havg_eq hnormalActual).signedHullLogVolume = perBThetaHullLog T b := by
  unfold PaperSignedHull.signedHullLogVolume paperSignedHullOfActualHullLog
  change -((A.logVolume A.hull).toReal) = perBThetaHullLog T b
  rw [hnormalActual]
  have hnon : 0 <= -perBThetaHullLog T b := by
    rw [← havg_eq]
    exact havg
  rw [ENNReal.toReal_ofReal hnon]
  ring

end LeanFormal.IUT.XiFPaper.S721ActualHullToPaperSignedHullActual
end