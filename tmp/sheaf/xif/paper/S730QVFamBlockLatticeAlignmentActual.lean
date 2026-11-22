import tmp.sheaf.xif.paper.S724QVFamBlockFractionalLatticeActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
/-! # S730: type alignment and Zp-smul for the qVFamily block lattice
Transports CommonPrimeCompletion memberships to NormalizedCompletion/rootBase
along the identity ring equivalence, and attempts the Zp-smul compatibility
needed for span induction. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S730QVFamBlockLatticeAlignmentActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S720OneFactorTensorNormReductionActual
open LeanFormal.IUT.XiFPaper.S724QVFamBlockFractionalLatticeActual
open LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.LocalFieldLogarithm
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
/-- Zp-smul compatibility for the one-factor tensor equivalence. -/
def QVFamBlockSMulCompatibility : Prop :=
  ∀ (z : ℤ_[qVFamTensorP T b]) (x : qVFamTensorBlock T b),
    qVFamBlockLinearEquiv (l := l) T b (z • x) =
      z • qVFamBlockLinearEquiv (l := l) T b x
