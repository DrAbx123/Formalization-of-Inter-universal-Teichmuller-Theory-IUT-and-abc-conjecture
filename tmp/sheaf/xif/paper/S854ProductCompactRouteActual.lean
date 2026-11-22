import tmp.sheaf.xif.paper.S853OInFZeroAbsorptionActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume

/-! # S854: product compactness route, no absorption

F(cRoot) compact is actual (S841).  O_hol is compact via
coefficient_arithmeticTupleHolomorphicLattice = canonicalUnitReference and
isCompact_arithmeticTupleCanonicalRegions.
The only remaining exact datum is compactness of the submodule product
F(cRoot)*O_hol.  Given that, paperRootMinimalRegion is compact and the S806
closedness gap follows.  No absorption and no product compactness is fabricated.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S854ProductCompactRouteActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.S806PaperRootHullNonzeroGapsActual
open LeanFormal.IUT.XiFPaper.S839PaperRootMinimalProductCompactActual
open LeanFormal.IUT.XiFPaper.S841FractionalCompactAbsorptionActual
open LeanFormal.IUT.XiFPaper.S853OInFZeroAbsorptionActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Actual compactness of O_hol from the canonical unit reference. -/
theorem s854HolomorphicCompact :
    IsCompact (s839HolomorphicLattice (l := l) T b : Set (qVFamTensorBlock T b)) := by
  unfold s839HolomorphicLattice
  rw [coefficient_arithmeticTupleHolomorphicLattice]
  exact (isCompact_arithmeticTupleCanonicalRegions
    (qVFamTensorPlaces T b) qVFamTensorTuple).2

/-- Exact product compactness datum. -/
def S854ProductCompact : Prop :=
  IsCompact ((s839FractionalLattice (l := l) T b *
    s839HolomorphicLattice (l := l) T b :
      Submodule ℤ_[(qVFamTensorP T b)] (qVFamTensorBlock T b)) :
        Set (qVFamTensorBlock T b))

/-- Exact O_hol <= F(0) alternative. -/
def S854OLeFractionalZero : Prop :=
  S853HolomorphicLeFractionalZero (l := l) T b

/-- Actual: the product-compactness datum implies minimal compactness. -/
theorem s854MinimalCompact_of_productCompact
    (h : S854ProductCompact (l := l) T b) :
    S839MinimalCompact (l := l) T b := by
  unfold S839MinimalCompact paperRootMinimalRegion rootThetaRegion
  rw [s839_thetaCoefficient_eq (l := l) T b]
  exact h

/-- Actual: the product-compactness datum closes the S806 gap. -/
theorem paperRootHullNonzeroClosedGap_of_productCompact
    (h : S854ProductCompact (l := l) T b) :
    PaperRootHullNonzeroClosedGap (l := l) T b :=
  paperRootHullNonzeroClosedGap_of_compact (l := l) T b
    (s854MinimalCompact_of_productCompact (l := l) T b h)

/-- Absorption (O_hol <= F(0)) also implies product compactness. -/
theorem s854ProductCompact_of_O_le_zero
    (h : S854OLeFractionalZero (l := l) T b) :
    S854ProductCompact (l := l) T b := by
  unfold S854ProductCompact
  have hpoint := s841PointwiseAbsorption_of_O_le_zero (l := l) T b h
  have habs := s841Absorption_of_pointwise (l := l) T b hpoint
  rw [habs]
  exact s841FractionalCompact (l := l) T b

/-- Exact remaining options: product compactness, or O_hol <= F(0). -/
def S854RemainingOptions : Prop :=
  S854ProductCompact (l := l) T b ∨ S854OLeFractionalZero (l := l) T b

end LeanFormal.IUT.XiFPaper.S854ProductCompactRouteActual

end
