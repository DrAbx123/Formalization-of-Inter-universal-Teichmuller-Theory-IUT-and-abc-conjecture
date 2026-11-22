/- R2 F-side hperB (independent construction): `actualLocalHullLog b <= packetV`
  by hull minimality/monotonicity (NO union-average shortcut).

  `actualLocalHullLog b` is the normalized log-volume of the actual root theta closure hull
  `actualLocalHullRegion b` on `qVFamTensorBlock T b`.  `packetV e istar varpi Phi` is the
  normalized log-volume of the Step-V holomorphic hull of the possible images on the same
  tensor block.  If the actual source map (route §4.2 step 3/5) gives
  `actualLocalHullRegion b ⊆ holomorphicHull (possiblyImages)`, hull monotonicity gives
  `actualLocalHullLog b <= packetV` (with positivity/finiteness of the hull Haar mass).
  LocalStepV data (`localRootLogVolume_eq`, `urRootAlpha_mass`) identify the per-b coefficient
  `(1/(2l)) log||q_b||` with the local root log volume.
  The containment is the named source-map input, kept explicit; no equality, no stub.
  No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1ULPacketVActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetActual
import tmp.sheaf.xif.paper.Mzk1G1F2R2LocalStepVActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 2000000
open scoped BigOperators
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.R2FiberHperBActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.Mzk1ULPacketVActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F2R2LocalStepVActual

universe u

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]
variable {J : Type} [Fintype J] {E : J → Type}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[qVFamTensorP T b] (E j)]
variable [∀ j, FiniteDimensional ℚ_[qVFamTensorP T b] (E j)] [∀ j, ProperSpace (E j)]

/-- **F-side hperB**: `actualLocalHullLog b <= packetV` from the source-map containment
    (hull minimality/monotonicity), with the actual Haar mass positivity/finiteness. -/
theorem actualLocalHullLog_le_packetV_of_containment
    (e : ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple ≃ₐ[ℚ_[qVFamTensorP T b]]
      ((j : J) → E j))
    (istar : qVFamTensorV) (varpi : CommonPrimeCompletion ((qVFamTensorPlaces T b) istar (qVFamTensorTuple istar)))
    (Phi : Set (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple ≃ₗ[ℚ_[qVFamTensorP T b]]
      ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple))
    (hcont : actualLocalHullRegion (l := l) T b ⊆
      arithmeticTupleHolomorphicHull (qVFamTensorPlaces T b) qVFamTensorTuple e
        (arithmeticTupleStepVPossibleImages (qVFamTensorPlaces T b) qVFamTensorTuple istar varpi Phi))
    (hpos : 0 < Measure.addHaar (arithmeticTupleHolomorphicHull (qVFamTensorPlaces T b) qVFamTensorTuple e
      (arithmeticTupleStepVPossibleImages (qVFamTensorPlaces T b) qVFamTensorTuple istar varpi Phi)))
    (hfin : Measure.addHaar (arithmeticTupleHolomorphicHull (qVFamTensorPlaces T b) qVFamTensorTuple e
      (arithmeticTupleStepVPossibleImages (qVFamTensorPlaces T b) qVFamTensorTuple istar varpi Phi)) < ⊤) :
    actualLocalHullLog (l := l) T b ≤ packetV e istar varpi Phi := by
  unfold actualLocalHullLog packetV
  exact arithmeticTupleNormalizedLogVolume_mono
    (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
    Measure.addHaar hcont hpos hfin

#print axioms actualLocalHullLog_le_packetV_of_containment

end LeanFormal.IUT.XiFPaper.R2FiberHperBActual