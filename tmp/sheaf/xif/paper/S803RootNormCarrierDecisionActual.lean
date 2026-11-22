import tmp.sheaf.xif.paper.S717TensorLatticeNormExactActual
import tmp.sheaf.xif.paper.S720OneFactorTensorNormReductionActual
import tmp.sheaf.xif.paper.S723OneFactorNormPreservingActual
import tmp.sheaf.xif.paper.S771RootNormCarrierActual
import tmp.sheaf.xif.paper.S784RootNormRegionsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S803RootNormCarrierDecisionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S717TensorLatticeNormExactActual
open LeanFormal.IUT.XiFPaper.S720OneFactorTensorNormReductionActual
open LeanFormal.IUT.XiFPaper.S723OneFactorNormPreservingActual
open LeanFormal.IUT.XiFPaper.S771RootNormCarrierActual
open LeanFormal.IUT.XiFPaper.S784RootNormRegionsActual
open LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.LocalFieldPadicTensor
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
variable (c : qVFamTensorV → Real)

/-- New-carrier norm target: on RootNormQVBlock the norm is by construction
the rootBase norm of the block map. -/
theorem rootNormCarrier_norm_eq_actual
    (x : RootNormQVBlock (T := T) b) :
    ‖x‖ = ‖rootNormLinearEquiv (l := l) T b x‖ := rfl

/-- The new-carrier fractional tensor lattice. -/
def RootNormTensorFractionalLattice : Set (RootNormQVBlock (T := T) b) :=
  rootNormSet (T := T) b
    (arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
      qVFamTensorTuple c)

/-- New-carrier norm bound replacing S717's old tensor norm lemma. -/
def RootNormTensorLatticeNormLe (R : Real) : Prop :=
  ∀ x : RootNormQVBlock (T := T) b,
    x ∈ RootNormTensorFractionalLattice (l := l) T b c → ‖x‖ ≤ R

/-- Exact S717/S720 maps-lattice condition remains on the old block. -/
def S803MapsLatticeGoal : Prop :=
  QVFamBlockMapsFractionalLattice (l := l) T b c

/-- Old-carrier norm preservation is not asserted; the new carrier replaces it. -/
def S803OldNormPreservingGoal : Prop :=
  QVFamBlockNormPreserving (l := l) T b

/-- New-carrier replacement of S723's norm-preserving goal: actual by rfl. -/
def S803RootNormPreservingActual : Prop :=
  ∀ x : RootNormQVBlock (T := T) b,
    ‖x‖ = ‖rootNormLinearEquiv (l := l) T b x‖

theorem s803RootNormPreservingActual_holds :
    S803RootNormPreservingActual (l := l) T b := by
  intro x
  exact rootNormCarrier_norm_eq_actual (l := l) T b x

/-- Exact remaining new-carrier norm bound: the root-norm lattice radius. -/
def S803RootNormLatticeBoundRequired (R : Real) : Prop :=
  RootNormTensorLatticeNormLe (l := l) T b c R

/-- S717's old tensor-lattice norm lemma is not transferred by norm equality;
the new carrier version is the exact bound above. -/
def S803OldTensorNormLemmaStatus : Prop :=
  TensorFractionalLatticeNormLemma (l := l) T b c

end LeanFormal.IUT.XiFPaper.S803RootNormCarrierDecisionActual

end
