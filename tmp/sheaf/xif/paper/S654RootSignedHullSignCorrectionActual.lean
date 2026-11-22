import tmp.sheaf.xif.paper.S657RootSignedHullIndependentActual

/-! # S654: thin compatibility layer over S657

The corrected sign/root signed-hull construction is S657.  This file keeps the
S654 names as aliases only; it no longer uses stale qVFamP or duplicate
processions. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S654RootSignedHullSignCorrectionActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S657RootSignedHullIndependentActual

universe uX
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

noncomputable abbrev rootThetaMagnitudeValue (j : SignedLabel l.value) : Real :=
  S657RootSignedHullIndependentActual.rootThetaMagnitudeValue T b j

theorem rootThetaMagnitudeValue_nonneg (j : SignedLabel l.value) :
    0 <= rootThetaMagnitudeValue T b j :=
  S657RootSignedHullIndependentActual.rootThetaMagnitudeValue_nonneg T b j

noncomputable abbrev rootThetaMagnitudeProcession :
    WeightedValues (SignedLabel l.value) :=
  S657RootSignedHullIndependentActual.rootThetaMagnitudeProcession T b

theorem rootThetaMagnitudeProcession_average_nonneg :
    0 <= (rootThetaMagnitudeProcession T b).average :=
  S657RootSignedHullIndependentActual.rootThetaMagnitudeProcession_average_nonneg T b

noncomputable abbrev rootThetaMagnitudeFiniteHull :
    FiniteHull (SignedLabel l.value) :=
  S657RootSignedHullIndependentActual.rootThetaMagnitudeFiniteHull T b

noncomputable abbrev rootNormalizedPaperSignedHullCorrected
    {X : Type uX} (A : IQHullLogVolumeInterface X)
    (hnormal : A.logVolume A.hull = ENNReal.ofReal
      (rootThetaMagnitudeProcession T b).average) :
    PaperSignedHull X (SignedLabel l.value) :=
  S657RootSignedHullIndependentActual.rootNormalizedPaperSignedHullCorrected
    T b A hnormal

theorem rootNormalizedPaperSignedHullCorrected_signed_eq
    {X : Type uX} (A : IQHullLogVolumeInterface X)
    (hnormal : A.logVolume A.hull = ENNReal.ofReal
      (rootThetaMagnitudeProcession T b).average) :
    (rootNormalizedPaperSignedHullCorrected T b A hnormal).signedHullLogVolume =
      -(rootThetaMagnitudeProcession T b).average :=
  S657RootSignedHullIndependentActual.rootNormalizedPaperSignedHullCorrected_signed_eq
    T b A hnormal

end LeanFormal.IUT.XiFPaper.S654RootSignedHullSignCorrectionActual
end
