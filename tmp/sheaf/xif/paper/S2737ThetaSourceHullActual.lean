import tmp.sheaf.xif.paper.S2725ThetaImageHullActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealSignedLogVolume
import tmp.sheaf.xif.paper.QVFamGlobalProductCarrierActual

noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2737ThetaSourceHullActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.QVFamGlobalProductCarrierActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- Actual source-hull signed log-volume, for the S2717 theta side. -/
noncomputable def S2737SourceThetaHullLogVolume
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) : Real :=
  I.sourceSignedHullLogVolume v R n

theorem S2737SourceThetaHullLogVolume_eq_neg_hullVolume
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    S2737SourceThetaHullLogVolume (I := I) v R n =
      -(I.sourceRealHullVolume v R n) :=
  I.sourceSignedHullLogVolume_eq_neg_hullSetVolume v R n

theorem S2737SourceThetaHullLogVolume_nonpos
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    S2737SourceThetaHullLogVolume (I := I) v R n <= 0 :=
  I.sourceSignedHullLogVolume_nonpos v R n

/-- Actual source image is contained in the actual source hull (S2725 object). -/
theorem S2737SourceThetaImage_subset_hull
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.possibleThetaPilotImageSet v R n ⊆
      (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) :=
I.possibleThetaPilotImage_subset_sourceHolomorphicHull v R n

/-- Actual mixed-prime global root hull scalar log, for the S2717 theta side. -/
noncomputable def S2737GlobalRootHullLog
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ (b : Bad (nativePlaceSelection T)), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ (b : Bad (nativePlaceSelection T)), BorelSpace (qVFamTensorBlock T b)]
    (mu : forall b, Measure (qVFamTensorBlock T b))
    (hmu : ∀ (b : Bad (nativePlaceSelection T)), Measure.IsAddHaarMeasure (mu b)) : Real :=
  letI := hmu
  globalRootHullLog (l := l) T mu

theorem S2737GlobalRootHullLog_eq
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ (b : Bad (nativePlaceSelection T)), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ (b : Bad (nativePlaceSelection T)), BorelSpace (qVFamTensorBlock T b)]
    (mu : forall b, Measure (qVFamTensorBlock T b))
    (hmu : ∀ (b : Bad (nativePlaceSelection T)), Measure.IsAddHaarMeasure (mu b)) :
    S2737GlobalRootHullLog (l := l) T mu hmu =
      globalRootHullLog (l := l) T mu :=
  letI := hmu
  rfl

#check S2737SourceThetaHullLogVolume
#check S2737SourceThetaHullLogVolume_eq_neg_hullVolume
#check S2737SourceThetaHullLogVolume_nonpos
#check S2737SourceThetaImage_subset_hull
#check S2737GlobalRootHullLog
#print axioms S2737SourceThetaHullLogVolume_eq_neg_hullVolume

end LeanFormal.IUT.XiFPaper.S2737ThetaSourceHullActual
end
