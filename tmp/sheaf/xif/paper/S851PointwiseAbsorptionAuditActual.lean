import tmp.sheaf.xif.paper.S841FractionalCompactAbsorptionActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalTensorLattice
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume

/-! # S851: F(cRoot) as O_hol-submodule (pointwise absorption)

S841PointwiseAbsorption is exactly the statement that F(cRoot) is closed
under multiplication by O_hol.  It is equivalent to the submodule product
inequality F(cRoot)*O_hol <= F(cRoot).  The reverse inequality is already
proved from 1 in O_hol.  The remaining mathematical fact is that the
fractional lattice F(cRoot) with cRoot >= 0 is an O_hol-module.
No module structure or absorption is fabricated. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S851PointwiseAbsorptionAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.S806PaperRootHullNonzeroGapsActual
open LeanFormal.IUT.XiFPaper.S839PaperRootMinimalProductCompactActual
open LeanFormal.IUT.XiFPaper.S841FractionalCompactAbsorptionActual
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

/-- Exact submodule-product inequality equivalent to pointwise absorption. -/
def S851FractionalMulLe : Prop :=
  s839FractionalLattice (l := l) T b * s839HolomorphicLattice (l := l) T b ≤
    s839FractionalLattice (l := l) T b

/-- S841 pointwise absorption is exactly the submodule-product inequality. -/
theorem s851Pointwise_iff_mulLe :
    S841PointwiseAbsorption (l := l) T b ↔ S851FractionalMulLe (l := l) T b := by
  unfold S841PointwiseAbsorption S851FractionalMulLe
  rw [Submodule.mul_le]

/-- Actual direction: submodule-product inequality gives S841 pointwise
absorption. -/
theorem s851Pointwise_of_mulLe
    (h : S851FractionalMulLe (l := l) T b) :
    S841PointwiseAbsorption (l := l) T b :=
  (s851Pointwise_iff_mulLe (l := l) T b).mpr h

/-- Exact algebraic module condition: F(cRoot) is closed under O_hol action. -/
def S851FractionalHolomorphicModule : Prop :=
  ∀ x : qVFamTensorBlock T b, x ∈ s839FractionalLattice (l := l) T b →
    ∀ y : qVFamTensorBlock T b, y ∈ s839HolomorphicLattice (l := l) T b →
      y * x ∈ s839FractionalLattice (l := l) T b

theorem s851Pointwise_iff_module :
    S841PointwiseAbsorption (l := l) T b ↔
      S851FractionalHolomorphicModule (l := l) T b := by
  unfold S841PointwiseAbsorption S851FractionalHolomorphicModule
  constructor
  · intro h x hx y hy
    rw [mul_comm]
    exact h x hx y hy
  · intro h x hx y hy
    rw [mul_comm]
    exact h x hx y hy

/-- Exact remaining O_hol-module/absorption lemma. -/
def S851O_holModuleRequired : Prop :=
  S851FractionalHolomorphicModule (l := l) T b

end LeanFormal.IUT.XiFPaper.S851PointwiseAbsorptionAuditActual

end
