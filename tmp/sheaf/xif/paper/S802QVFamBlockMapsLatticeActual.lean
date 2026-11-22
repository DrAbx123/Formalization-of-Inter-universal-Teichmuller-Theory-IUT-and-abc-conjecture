import tmp.sheaf.xif.paper.S724QVFamBlockFractionalLatticeActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicSubmoduleTensor
/-! # S802: actual QVFamBlockMapsFractionalLattice via span_le/comap
Uses the scoped Zp module and the pure-tensor identity
qVFamBlockLinearEquiv_tprod.  No span_induction. -/
noncomputable section
open scoped BigOperators LeanFormal.IUT.FinitePadicIntegralLattice
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000
namespace LeanFormal.IUT.XiFPaper.S802QVFamBlockMapsLatticeActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S720OneFactorTensorNormReductionActual
open LeanFormal.IUT.XiFPaper.S724QVFamBlockFractionalLatticeActual
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
variable (c : qVFamTensorV → Real)
/-- Pure tensor image lies in the local fractional lattice. -/
theorem pureTensor_mem_fractionalLattice
    (f : (i : qVFamTensorV) →
      CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i)))
    (hf : ∀ i, f i ∈ padicFractionalLattice (p := qVFamTensorP T b)
      (K := CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i)))
        (c i)) :
    (qVFamBlockLinearEquiv (l := l) T b
      (finitePadicTensorTprod (p := qVFamTensorP T b)
        (fun i => CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i))) f) :
      rootBase T b) ∈ padicFractionalLattice (p := qVFamTensorP T b)
        (K := rootBase T b) (∑ i, c i) := by
  rw [qVFamBlockLinearEquiv_tprod]
  simpa [qVFamTensorV, Finset.sum_const, Finset.card_univ] using hf ()
/-- Actual QVFamBlockMapsFractionalLattice. -/
theorem qVFamBlockMapsFractionalLattice_actual :
    QVFamBlockMapsFractionalLattice (l := l) T b c := by
  intro x hx
  change x ∈ Submodule.span ℤ_[qVFamTensorP T b]
    (tensorIntegralRegion (p := qVFamTensorP T b)
      (fun i => CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i)))
      (fun i => (padicFractionalLattice (p := qVFamTensorP T b)
        (K := CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i)))
          (c i) : Set _))) at hx
  have hspan : Submodule.span ℤ_[qVFamTensorP T b]
      (tensorIntegralRegion (p := qVFamTensorP T b)
        (fun i => CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i)))
        (fun i => (padicFractionalLattice (p := qVFamTensorP T b)
          (K := CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i)))
            (c i) : Set _))) ≤
      Submodule.comap (qVFamBlockLinearEquiv (l := l) T b).toLinearMap
        (padicFractionalLattice (p := qVFamTensorP T b) (K := rootBase T b)
          (∑ i, c i)) := by
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact pureTensor_mem_fractionalLattice (l := l) T b c f hf
  exact hspan hx
end LeanFormal.IUT.XiFPaper.S802QVFamBlockMapsLatticeActual
