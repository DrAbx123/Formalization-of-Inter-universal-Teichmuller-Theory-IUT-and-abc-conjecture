import tmp.sheaf.xif.paper.S730QVFamBlockLatticeAlignmentActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
/-! # S738: transport CommonPrimeCompletion lattice membership to rootBase
Uses the identity ring equivalence and its actual isometry to prove the
S730 alignment. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S738QVFamBlockAlignmentActualAdapted
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S720OneFactorTensorNormReductionActual
open LeanFormal.IUT.XiFPaper.S730QVFamBlockLatticeAlignmentActual
open LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.LocalFieldLogarithm
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
/-- Exact type alignment datum of S730. -/
def CommonPrimeNormalizedLatticeAlignment : Prop :=
  ∀ (a : Real) (y : CommonPrimeCompletion (qVFamTensorPlaces T b () ())),
    y ∈ padicFractionalLattice (p := qVFamTensorP T b)
      (K := CommonPrimeCompletion (qVFamTensorPlaces T b () ())) a →
      (commonPrimeCompletionRingEquiv (qVFamTensorPlaces T b () ()) y :
        rootBase T b) ∈ padicFractionalLattice (p := qVFamTensorP T b)
          (K := rootBase T b) a
theorem commonPrimeCompletionRingEquiv_norm
    (y : CommonPrimeCompletion (qVFamTensorPlaces T b () ())) :
    ‖(commonPrimeCompletionRingEquiv (qVFamTensorPlaces T b () ()) y :
      rootBase T b)‖ = ‖y‖ := by
  have h := (isometry_commonPrimeCompletionRingEquiv
    (qVFamTensorPlaces T b () ())).norm_map_of_map_zero (map_zero _) y
  simpa [commonPrimeCompletionRingEquiv, qVFamTensorPlaces] using h
theorem commonPrimeNormalizedLatticeAlignment_actual :
    CommonPrimeNormalizedLatticeAlignment T b := by
  intro a y hy
  change (commonPrimeCompletionRingEquiv (qVFamTensorPlaces T b () ()) y :
    NormalizedCompletion ((qVFamTensorPlaces T b () ()).val)) ∈
      padicFractionalLattice (p := qVFamTensorP T b)
        (K := NormalizedCompletion ((qVFamTensorPlaces T b () ()).val)) a
  rw [mem_padicFractionalLattice_iff] at hy ⊢
  rw [commonPrimeCompletionRingEquiv_norm (l := l) T b y]
  exact hy
end LeanFormal.IUT.XiFPaper.S738QVFamBlockAlignmentActualAdapted
