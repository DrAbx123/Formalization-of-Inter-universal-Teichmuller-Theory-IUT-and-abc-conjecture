import tmp.sheaf.xif.paper.S717TensorLatticeNormExactActual
import tmp.sheaf.xif.paper.S312QPilotRootTensorBaseChangeActual
import LeanFormal.IUT.Foundations.LocalFields.PadicFractionalLattice
/-! # S720: one-factor reduction of TensorFractionalLatticeNormLemma
For qVFamTensorV = Unit, the tensor equivalence qVFamBlockLinearEquiv maps the
fractional tensor lattice to the local padic fractional norm ball.  The local
norm-ball lemma then gives the bound, conditional on the equivalence mapping
the lattice into the local ball and preserving norms.  These two conditions
are recorded exactly; no false isometry is asserted. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.S720OneFactorTensorNormReductionActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S668QPilotRootExtensionPerBActual
open LeanFormal.IUT.XiFPaper.S692QPilotRegionNormExactActual
open LeanFormal.IUT.XiFPaper.S708QPilotRootLabelRegionNormActual
open LeanFormal.IUT.XiFPaper.S717TensorLatticeNormExactActual
open LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
variable (c : qVFamTensorV → Real)
/-- One-factor local image condition: the tensor fractional lattice maps into
the local padic fractional ball of exponent sum c. -/
def QVFamBlockMapsFractionalLattice : Prop :=
  ∀ x ∈ arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
    qVFamTensorTuple c,
      (qVFamBlockLinearEquiv (l := l) T b x : rootBase T b) ∈
        padicFractionalLattice (p := qVFamTensorP T b) (K := rootBase T b)
          (∑ i, c i)
/-- One-factor norm-preservation on the tensor block. -/
def QVFamBlockNormPreserving : Prop :=
  ∀ x : qVFamTensorBlock T b,
    ‖x‖ = ‖(qVFamBlockLinearEquiv (l := l) T b x : rootBase T b)‖
/-- Local norm-ball lemma for the padic fractional lattice. -/
theorem padicFractionalLattice_norm_le
    (a : Real) {y : rootBase T b}
    (hy : y ∈ padicFractionalLattice (p := qVFamTensorP T b)
      (K := rootBase T b) a) :
    ‖y‖ ≤ Real.rpow (qVFamTensorP T b : Real) (-a) := by
  rw [mem_padicFractionalLattice_iff] at hy
  exact hy
/-- One-factor reduction: local image + norm preservation imply the tensor
fractional-lattice norm lemma. -/
theorem tensorFractionalLatticeNormLemma_of_oneFactor
    (hmap : QVFamBlockMapsFractionalLattice (l := l) T b c)
    (hpres : QVFamBlockNormPreserving (l := l) T b) :
    TensorFractionalLatticeNormLemma (l := l) T b c := by
  intro x hx
  rw [hpres x]
  exact padicFractionalLattice_norm_le (l := l) T b (∑ i, c i) (hmap x hx)
/-- Exact one-factor data still needed. -/
structure OneFactorTensorNormData where
  maps_lattice : QVFamBlockMapsFractionalLattice (l := l) T b c
  norm_preserving : QVFamBlockNormPreserving (l := l) T b
/-- Exact minimal remaining data. -/
def S720ExactGoal : Prop :=
  Nonempty (OneFactorTensorNormData (l := l) T b c)
/-- The exact data implies S717's tensor norm lemma. -/
theorem tensorFractionalLatticeNormLemma_of_data
    (D : OneFactorTensorNormData (l := l) T b c) :
    TensorFractionalLatticeNormLemma (l := l) T b c :=
  tensorFractionalLatticeNormLemma_of_oneFactor (l := l) T b c
    D.maps_lattice D.norm_preserving
end LeanFormal.IUT.XiFPaper.S720OneFactorTensorNormReductionActual
