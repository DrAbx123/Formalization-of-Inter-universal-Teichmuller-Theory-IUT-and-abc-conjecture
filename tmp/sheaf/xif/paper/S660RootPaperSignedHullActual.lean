import tmp.sheaf.xif.paper.S657RootSignedHullIndependentActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S660RootPaperSignedHullActual

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

/-- Actual paper signed hull from the S657 root-normalized procession and the
ambient IQ hull interface. -/
noncomputable def s660PaperSignedHull
    {X : Type uX} (A : IQHullLogVolumeInterface X)
    (hnormal : A.logVolume A.hull = ENNReal.ofReal
      (rootThetaMagnitudeProcession T b).average) :
    PaperSignedHull X (SignedLabel l.value) :=
  rootNormalizedPaperSignedHullCorrected T b A hnormal

/-- The actual signed hull log-volume is the negative of the root-normalized
procession average. -/
theorem s660_signedHullLogVolume_eq_neg_average
    {X : Type uX} (A : IQHullLogVolumeInterface X)
    (hnormal : A.logVolume A.hull = ENNReal.ofReal
      (rootThetaMagnitudeProcession T b).average) :
    (s660PaperSignedHull T b A hnormal).signedHullLogVolume =
      -(rootThetaMagnitudeProcession T b).average :=
  rootNormalizedPaperSignedHullCorrected_signed_eq T b A hnormal

end LeanFormal.IUT.XiFPaper.S660RootPaperSignedHullActual

end
