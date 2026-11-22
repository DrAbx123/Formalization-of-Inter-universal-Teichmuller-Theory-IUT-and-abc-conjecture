import tmp.sheaf.xif.paper.S657RootSignedHullIndependentActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S658RootNormalizedPaperSignedHullActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S657RootSignedHullIndependentActual
open MeasureTheory

universe uX
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Corrected root-normalized paper signed hull on the S657 positive magnitude
procession, given the ambient log-volume interface and its normalization. -/
noncomputable def rootNormalizedPaperSignedHullCorrected
    {X : Type uX} (A : IQHullLogVolumeInterface X)
    (hnormal : A.logVolume A.hull = ENNReal.ofReal
      (rootThetaMagnitudeProcession T b).average) :
    PaperSignedHull X (SignedLabel l.value) where
  ambient := A
  procession := rootThetaMagnitudeProcession T b
  hull := rootThetaMagnitudeFiniteHull T b
  weighted_matches_hull := by intro j; rfl
  weights_nonnegative := by intro _; exact inv_nonneg.mpr (Nat.cast_nonneg _)
  average_nonneg := rootThetaMagnitudeProcession_average_nonneg T b
  hull_logVolume_eq_average := hnormal

/-- The signed hull log-volume is the negative of the positive-magnitude
procession average. -/
theorem rootNormalizedPaperSignedHullCorrected_signed_eq
    {X : Type uX} (A : IQHullLogVolumeInterface X)
    (hnormal : A.logVolume A.hull = ENNReal.ofReal
      (rootThetaMagnitudeProcession T b).average) :
    (rootNormalizedPaperSignedHullCorrected T b A hnormal).signedHullLogVolume =
      -(rootThetaMagnitudeProcession T b).average := by
  unfold PaperSignedHull.signedHullLogVolume rootNormalizedPaperSignedHullCorrected
  rw [hnormal, ENNReal.toReal_ofReal (rootThetaMagnitudeProcession_average_nonneg T b)]

end LeanFormal.IUT.XiFPaper.S658RootNormalizedPaperSignedHullActual

end
