import tmp.sheaf.xif.paper.S839PaperRootMinimalProductCompactActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalTensorLattice
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicSubmoduleTensor
import LeanFormal.IUT.Foundations.LocalFields.PadicFractionalLattice

/-! # S841: fractional compactness and absorption

(1) S839FractionalCompact is proved from compact local fractional lattices
    and isCompact_submoduleTensorSpan.
(2) S839ProductAbsorption is reduced to the exact pointwise ideal absorption
    F * O_hol <= F; the reverse F <= F * O_hol follows from 1 in O_hol.
No absorption or compactness is fabricated. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S841FractionalCompactAbsorptionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S806PaperRootHullNonzeroGapsActual
open LeanFormal.IUT.XiFPaper.S839PaperRootMinimalProductCompactActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
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

/-- Actual compactness of the paper fractional lattice F(cRoot). -/
theorem s841FractionalCompact :
    S839FractionalCompact (l := l) T b := by
  unfold S839FractionalCompact s839FractionalLattice
  apply isCompact_submoduleTensorSpan
  intro i
  exact isCompact_padicFractionalLattice_of_nonneg
    (p := qVFamTensorP T b)
    (K := CommonPrimeCompletion ((qVFamTensorPlaces T b) i (qVFamTensorTuple i)))
    (paperRootCoefficientFamily (l := l) T b i)
    (paperRootCoefficientFamily_nonneg (l := l) T b i)

/-- Exact pointwise ideal absorption F * O_hol <= F. -/
def S841PointwiseAbsorption : Prop :=
  ∀ x : qVFamTensorBlock T b, x ∈ s839FractionalLattice (l := l) T b →
    ∀ y : qVFamTensorBlock T b, y ∈ s839HolomorphicLattice (l := l) T b →
      x * y ∈ s839FractionalLattice (l := l) T b

/-- Pointwise ideal absorption implies the submodule product absorption. -/
theorem s841Absorption_of_pointwise
    (h : S841PointwiseAbsorption (l := l) T b) :
    S839ProductAbsorption (l := l) T b := by
  unfold S839ProductAbsorption
  apply le_antisymm
  · rw [Submodule.mul_le]
    exact h
  · intro x hx
    have hone : (1 : qVFamTensorBlock T b) ∈ s839HolomorphicLattice (l := l) T b := by
      unfold s839HolomorphicLattice arithmeticTupleHolomorphicLattice
      exact (integralClosure ℤ_[(qVFamTensorP T b)]
        (qVFamTensorBlock T b)).one_mem
    simpa using Submodule.mul_mem_mul hx hone

/-- Conditional product absorption route. -/
theorem s839ProductAbsorption_of_pointwise
    (h : S841PointwiseAbsorption (l := l) T b) :
    S839ProductAbsorption (l := l) T b :=
  s841Absorption_of_pointwise (l := l) T b h

/-- Conditional closure of the S806 closedness gap from pointwise absorption. -/
theorem paperRootHullNonzeroClosedGap_of_pointwise_absorption
    (h : S841PointwiseAbsorption (l := l) T b) :
    PaperRootHullNonzeroClosedGap (l := l) T b :=
  paperRootHullNonzeroClosedGap_of_product_compact (l := l) T b
    (s841Absorption_of_pointwise (l := l) T b h)
    (s841FractionalCompact (l := l) T b)

end LeanFormal.IUT.XiFPaper.S841FractionalCompactAbsorptionActual

end
