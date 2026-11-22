/- F-side hperB (`FsideHperBActual`): `actualLocalHullLog T b <= packetV b` per bad place.

  A: `actualLocalHullLog T b` is the normalized log-volume of the actual root theta closure
     hull `actualLocalHullRegion T b` on the F-side block `qVFamTensorBlock T b`
     (`PaperLevelXiFTargetActual`), with the LocalStepV identification
     `localRootLogVolume_eq` of its `(1/(2l)) log||q_b||` coefficient.
  B: `packetV e istar varpi Phi` (`Mzk1ULPacketVActual`) is david's actual F-side packet
     value: the normalized log-volume of the Step-V holomorphic hull of the possible images
     on the same block.
  A2: if the actual source map gives the region containment
     `actualLocalHullRegion T b ⊆ holomorphicHull (possibleImages)` (route §4.2 step 3/5),
     hull monotonicity (`arithmeticTupleNormalizedLogVolume_mono`) yields the per-b
     inequality.  The containment is the named source-map input, kept explicit.
  The weighted consumption is the DONE `Mzk1P6P5ThetaHullControl2.thetaHullLog_le_ucHpkt`.
  No equality, no stub, no sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1ULPacketVActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetActual
import tmp.sheaf.xif.paper.Mzk1P6P5ThetaHullControl2
import tmp.sheaf.xif.paper.Mzk1UCC3ProducerActual
import tmp.sheaf.xif.paper.Mzk1G1F2R2LocalStepVActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 2000000
open scoped BigOperators
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.FsideHperBActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.Mzk1ULPacketVActual
open LeanFormal.IUT.XiFPaper.Mzk1P6P5ThetaHullControl2
open LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual
open LeanFormal.IUT.LocalFieldProductHull

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]
variable {J : Type} [Fintype J] {E : J → Type}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[qVFamTensorP T b] (E j)]
variable [∀ j, FiniteDimensional ℚ_[qVFamTensorP T b] (E j)] [∀ j, ProperSpace (E j)]

/-- **A2 (per b)**: source-map containment gives `actualLocalHullLog b <= packetV b` by
    hull minimality/monotonicity, with the hull Haar mass positivity/finiteness. -/
theorem actualLocalHullLog_le_packetV_of_containment
    (e : ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple ≃ₐ[ℚ_[qVFamTensorP T b]]
      ((j : J) → E j))
    (istar : qVFamTensorV)
    (varpi : CommonPrimeCompletion ((qVFamTensorPlaces T b) istar (qVFamTensorTuple istar)))
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

/-- **B + consumption**: the per-b F-side hperB yields the weighted theta-hull bound
    against the F-side packet sum (DONE `thetaHullLog_le_ucHpkt`). -/
theorem fside_thetaHull_le_ucHpkt
    (V : Bad (nativePlaceSelection T) → ℝ)
    (hperB : ∀ b, actualLocalHullLog (l := l) T b ≤ V b) :
    actualThetaHullLogRoot (l := l) T ≤ ucWeightedHpkt (nativeBadLocalWeight T) V :=
  thetaHullLog_le_ucHpkt (l := l) T V hperB

#print axioms actualLocalHullLog_le_packetV_of_containment
#print axioms fside_thetaHull_le_ucHpkt


/-- The Step-V holomorphic hull is closed (image under `e.symm` of the closed product hull). -/
theorem isClosed_arithmeticTupleHolomorphicHull'
    (e : ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple ≃ₐ[ℚ_[qVFamTensorP T b]]
      ((j : J) → E j))
    (A : Set (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple)) :
    IsClosed (arithmeticTupleHolomorphicHull (qVFamTensorPlaces T b) qVFamTensorTuple e A) := by
  have hr : LocalFieldProductHull.hull (e '' A) =
      ⋂ lam : (i : J) → E i, ⋂ (_ : ∀ i, lam i ≠ 0),
        ⋂ (_ : e '' A ⊆ LocalFieldProductHull.region lam), LocalFieldProductHull.region lam := by
    ext x
    simp [LocalFieldProductHull.hull]
  have hHull : IsClosed (LocalFieldProductHull.hull (e '' A)) := by
    rw [hr]
    exact isClosed_iInter fun lam => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      (isCompact_region lam).isClosed
  unfold arithmeticTupleHolomorphicHull
  have himg : e.symm '' (LocalFieldProductHull.hull (e '' A)) =
      e ⁻¹' (LocalFieldProductHull.hull (e '' A)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨e x, by simpa using hx, by simp⟩
  rw [himg]
  have hcont : Continuous (e : ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple → ((j : J) → E j)) :=
    LinearMap.continuous_of_finiteDimensional
      (e.toLinearEquiv : ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple →ₗ[ℚ_[qVFamTensorP T b]] ((j : J) → E j))
  exact hHull.preimage hcont

/-- **Containment reduction**: if each actual root theta row region `j` lies in the Step-V
    holomorphic hull of the possible images (the Ind1/Ind2 source-action input), then the
    actual root theta closure hull `actualLocalHullRegion` does too (closure of a union inside
    a closed set). -/
theorem actualLocalHullRegion_subset_hull_of_rows
    (e : ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple ≃ₐ[ℚ_[qVFamTensorP T b]]
      ((j : J) → E j))
    (istar : qVFamTensorV)
    (varpi : CommonPrimeCompletion ((qVFamTensorPlaces T b) istar (qVFamTensorTuple istar)))
    (Phi : Set (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple ≃ₗ[ℚ_[qVFamTensorP T b]]
      ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple))
    (hrows : ∀ j : SignedLabel l.value,
      actualRootThetaRegion (l := l) T b j ⊆
        arithmeticTupleHolomorphicHull (qVFamTensorPlaces T b) qVFamTensorTuple e
          (arithmeticTupleStepVPossibleImages (qVFamTensorPlaces T b) qVFamTensorTuple istar varpi Phi)) :
    actualLocalHullRegion (l := l) T b ⊆
      arithmeticTupleHolomorphicHull (qVFamTensorPlaces T b) qVFamTensorTuple e
        (arithmeticTupleStepVPossibleImages (qVFamTensorPlaces T b) qVFamTensorTuple istar varpi Phi) := by
  unfold actualLocalHullRegion actualRootThetaHull
  exact closure_minimal (Set.iUnion_subset hrows)
    (isClosed_arithmeticTupleHolomorphicHull' (l := l) T b e _)

#print axioms isClosed_arithmeticTupleHolomorphicHull'
#print axioms actualLocalHullRegion_subset_hull_of_rows

end LeanFormal.IUT.XiFPaper.FsideHperBActual