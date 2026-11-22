import tmp.sheaf.xif.paper.S806PaperRootHullNonzeroGapsActual
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalTensorLattice
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIntegerTensorComparison

/-! # S839: product compactness for the paper root minimal region

paperRootMinimalRegion = F(cRoot) * O_hol, with the j=1 gauss exponent
absorbed because gaussExponent oneLabel = 1.  F(cRoot) is a fractional
lattice and O_hol is the holomorphic lattice.

Exact minimal condition used here: F(cRoot) * O_hol = F(cRoot)
(absorption).  Then the minimal region is the fractional lattice set, and
compactness of F(cRoot) gives IsCompact paperRootMinimalRegion, hence the
S806 closedness gap.
No compactness or absorption is fabricated. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S839PaperRootMinimalProductCompactActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.S806PaperRootHullNonzeroGapsActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Fractional lattice F(cRoot). -/
noncomputable def s839FractionalLattice : Submodule ℤ_[(qVFamTensorP T b)]
    (qVFamTensorBlock T b) :=
  arithmeticTupleFractionalLattice (qVFamTensorPlaces T b) qVFamTensorTuple
    (paperRootCoefficientFamily (l := l) T b)

/-- Holomorphic lattice O_hol. -/
noncomputable def s839HolomorphicLattice : Submodule ℤ_[(qVFamTensorP T b)]
    (qVFamTensorBlock T b) :=
  arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple

/-- Exact absorption condition. -/
def S839ProductAbsorption : Prop :=
  s839FractionalLattice (l := l) T b * s839HolomorphicLattice (l := l) T b =
    s839FractionalLattice (l := l) T b

/-- Exact fractional-lattice compactness condition. -/
def S839FractionalCompact : Prop :=
  IsCompact (s839FractionalLattice (l := l) T b : Set (qVFamTensorBlock T b))

/-- Exact minimal compactness target. -/
def S839MinimalCompact : Prop :=
  IsCompact (paperRootMinimalRegion (l := l) T b)

/-- The j=1 coefficient function is the paper root coefficient family. -/
theorem s839_thetaCoefficient_eq :
    (fun i : qVFamTensorV =>
      ((gaussExponent (oneLabel l).1).toNat : Real) *
        paperRootCoefficientFamily (l := l) T b i) =
    paperRootCoefficientFamily (l := l) T b := by
  funext i
  rw [gaussExponent_oneLabel l]
  norm_num

/-- Under absorption, paperRootMinimalRegion is exactly the fractional
lattice carrier. -/
theorem paperRootMinimalRegion_eq_fractional_of_absorption
    (h : S839ProductAbsorption (l := l) T b) :
    paperRootMinimalRegion (l := l) T b =
      (s839FractionalLattice (l := l) T b : Set (qVFamTensorBlock T b)) := by
  unfold paperRootMinimalRegion rootThetaRegion
  rw [s839_thetaCoefficient_eq (l := l) T b]
  change ((s839FractionalLattice (l := l) T b *
      s839HolomorphicLattice (l := l) T b : Submodule ℤ_[(qVFamTensorP T b)]
        (qVFamTensorBlock T b)) : Set (qVFamTensorBlock T b)) =
    (s839FractionalLattice (l := l) T b : Set (qVFamTensorBlock T b))
  rw [h]

/-- Product compactness route: absorption + fractional compactness gives the
paperRootMinimalRegion compactness. -/
theorem paperRootMinimalRegion_compact_of_absorption
    (habs : S839ProductAbsorption (l := l) T b)
    (hF : S839FractionalCompact (l := l) T b) :
    S839MinimalCompact (l := l) T b := by
  unfold S839MinimalCompact
  rw [paperRootMinimalRegion_eq_fractional_of_absorption (l := l) T b habs]
  exact hF

/-- And hence the S806 closedness gap. -/
theorem paperRootHullNonzeroClosedGap_of_product_compact
    (habs : S839ProductAbsorption (l := l) T b)
    (hF : S839FractionalCompact (l := l) T b) :
    PaperRootHullNonzeroClosedGap (l := l) T b :=
  paperRootHullNonzeroClosedGap_of_compact (l := l) T b
    (paperRootMinimalRegion_compact_of_absorption (l := l) T b habs hF)

end LeanFormal.IUT.XiFPaper.S839PaperRootMinimalProductCompactActual

end
