import tmp.sheaf.xif.paper.S1574ProductImageAbsorptionActual
import tmp.sheaf.xif.paper.S839PaperRootMinimalProductCompactActual
import tmp.sheaf.xif.paper.S853OInFZeroAbsorptionActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIntegerTensorComparison
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlockFields
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalTensorLattice

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1579OLeFractionalZeroAnalysisActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S839PaperRootMinimalProductCompactActual
open LeanFormal.IUT.XiFPaper.S853OInFZeroAbsorptionActual
open LeanFormal.IUT.XiFPaper.S841FractionalCompactAbsorptionActual
open LeanFormal.IUT.XiFPaper.S863ProductImageCompactActual
open LeanFormal.IUT.XiFPaper.S1574ProductImageAbsorptionActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (N8Closure.nativePlaceSelection T))]
variable [∀ b : Bad (N8Closure.nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (N8Closure.nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (N8Closure.nativePlaceSelection T))

/-- F(0) is exactly the tensor valuation-integer lattice (actual). -/
theorem s1579FractionalZero_eq_integerLattice :
    s853FractionalZero (l := l) T b =
      arithmeticTupleValuationIntegerLattice (qVFamTensorPlaces T b) qVFamTensorTuple :=
  arithmeticTupleFractionalLattice_zero (qVFamTensorPlaces T b) qVFamTensorTuple

/-- Actual reverse inclusion: F(0) is contained in O_hol (the direction that
is available in the tree). -/
theorem s1579IntegerLattice_le_holomorphic :
    s853FractionalZero (l := l) T b ≤ s839HolomorphicLattice (l := l) T b := by
  rw [s1579FractionalZero_eq_integerLattice]
  obtain ⟨J, hJ, E, hfield, halgebra, e, hprops⟩ :=
    exists_arithmeticTensorTuple_fieldProduct (qVFamTensorPlaces T b) qVFamTensorTuple
  letI := hJ
  letI := hfield
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[qVFamTensorP T b] (E j) := fun j => (hprops.1 j).1
  letI : ∀ j, ProperSpace (E j) := fun j =>
    FiniteDimensional.proper ℚ_[qVFamTensorP T b] (E j)
  letI : ∀ j, IsUltrametricDist (E j) := fun j => (hprops.1 j).2.2
  intro x hx
  have h := arithmeticTupleValuationIntegerLattice_subset_canonicalUnitReference
    (qVFamTensorPlaces T b) qVFamTensorTuple e hx
  rwa [← coefficient_arithmeticTupleHolomorphicLattice] at h

/-- Exact forward inclusion needed for S841/S853.  No proof is available from
the reverse inclusion, and no counterexample is asserted. -/
def S1579ForwardInclusionRequired : Prop :=
  S853OLeFractionalZeroRequired (l := l) T b

/-- The exact forward inclusion gives S841 pointwise absorption via S853. -/
theorem s1579PointwiseAbsorption_of_forward
    (h : S1579ForwardInclusionRequired (l := l) T b) :
    S841PointwiseAbsorption T b :=
  s1574PointwiseAbsorption_of_OLeZero T b h

/-- The exact forward inclusion gives S863ProductImageEq via S1570. -/
theorem s1579ProductImageEq_of_forward
    (h : S1579ForwardInclusionRequired (l := l) T b) :
    S863ProductImageEq T b :=
  s1574ProductImageEq_of_OLeZero T b h

end LeanFormal.IUT.XiFPaper.S1579OLeFractionalZeroAnalysisActual

end
