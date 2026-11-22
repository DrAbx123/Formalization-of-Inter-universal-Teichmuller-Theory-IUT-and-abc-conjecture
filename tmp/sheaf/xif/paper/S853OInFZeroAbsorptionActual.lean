import tmp.sheaf.xif.paper.S851PointwiseAbsorptionAuditActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalTensorLattice
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly

/-! # S853: absorption from O_hol <= F(0)

If O_hol <= F(0) = arithmeticTupleValuationIntegerLattice, then
  F(cRoot) * O_hol <= F(cRoot) * F(0) <= F(cRoot)
by arithmeticTupleFractionalLattice_mul_le.  This gives pointwise absorption
and hence the S806 closedness gap.
The exact remaining inclusion is O_hol <= F(0); only the reverse F(0) <= O_hol
is available in the project.  No inclusion is fabricated. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S853OInFZeroAbsorptionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.S806PaperRootHullNonzeroGapsActual
open LeanFormal.IUT.XiFPaper.S839PaperRootMinimalProductCompactActual
open LeanFormal.IUT.XiFPaper.S841FractionalCompactAbsorptionActual
open LeanFormal.IUT.XiFPaper.S851PointwiseAbsorptionAuditActual
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

/-- F(0) is the valuation integer lattice. -/
noncomputable def s853FractionalZero : Submodule ℤ_[(qVFamTensorP T b)]
    (qVFamTensorBlock T b) :=
  arithmeticTupleFractionalLattice (qVFamTensorPlaces T b) qVFamTensorTuple
    (fun _ => 0)

/-- Exact needed inclusion O_hol <= F(0). -/
def S853HolomorphicLeFractionalZero : Prop :=
  s839HolomorphicLattice (l := l) T b ≤ s853FractionalZero (l := l) T b

/-- Exact composition lemma: F(c)*O_hol <= F(c). -/
def S853FractionalMulHolomorphicLe : Prop :=
  s839FractionalLattice (l := l) T b * s839HolomorphicLattice (l := l) T b ≤
    s839FractionalLattice (l := l) T b

/-- O_hol <= F(0) implies F(c)*O_hol <= F(c). -/
theorem s853FractionalMulHolomorphicLe_of_O_le_zero
    (h : S853HolomorphicLeFractionalZero (l := l) T b) :
    S853FractionalMulHolomorphicLe (l := l) T b := by
  unfold S853FractionalMulHolomorphicLe
  have hmul : s839FractionalLattice (l := l) T b * s839HolomorphicLattice (l := l) T b ≤
      s839FractionalLattice (l := l) T b * s853FractionalZero (l := l) T b :=
    mul_le_mul' le_rfl h
  have hzero : s839FractionalLattice (l := l) T b * s853FractionalZero (l := l) T b ≤
      s839FractionalLattice (l := l) T b := by
    unfold s839FractionalLattice s853FractionalZero
    simpa using arithmeticTupleFractionalLattice_mul_le
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (paperRootCoefficientFamily (l := l) T b) (fun _ : qVFamTensorV => 0)
  exact hmul.trans hzero

/-- Conditional pointwise absorption. -/
theorem s841PointwiseAbsorption_of_O_le_zero
    (h : S853HolomorphicLeFractionalZero (l := l) T b) :
    S841PointwiseAbsorption (l := l) T b := by
  intro x hx y hy
  have hmul := s853FractionalMulHolomorphicLe_of_O_le_zero (l := l) T b h
  exact hmul (Submodule.mul_mem_mul hx hy)

/-- Conditional closure of the S806 closedness gap. -/
theorem paperRootHullNonzeroClosedGap_of_O_le_zero
    (h : S853HolomorphicLeFractionalZero (l := l) T b) :
    PaperRootHullNonzeroClosedGap (l := l) T b :=
  paperRootHullNonzeroClosedGap_of_pointwise_absorption (l := l) T b
    (s841PointwiseAbsorption_of_O_le_zero (l := l) T b h)

/-- Exact remaining project lemma: O_hol <= F(0). -/
def S853OLeFractionalZeroRequired : Prop :=
  S853HolomorphicLeFractionalZero (l := l) T b

end LeanFormal.IUT.XiFPaper.S853OInFZeroAbsorptionActual

end
