import tmp.sheaf.xif.paper.S724QVFamBlockFractionalLatticeActual
import tmp.sheaf.xif.paper.S741QVFamBlockSMulActual
import LeanFormal.IUT.LocalFieldPadicTensor
/-! # S772: image containment by span induction, no isometry
Reduces QVFamBlockMapsFractionalLattice to the pure-tensor image statement and
proves the norm bound from membership in padicFractionalLattice.  The Zp-smul
step uses S741.  No norm equality/isometry is required. -/
noncomputable section
open scoped BigOperators LeanFormal.IUT.FinitePadicIntegralLattice
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000
namespace LeanFormal.IUT.XiFPaper.S772QVFamBlockMapsLatticeActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S720OneFactorTensorNormReductionActual
open LeanFormal.IUT.XiFPaper.S724QVFamBlockFractionalLatticeActual
open LeanFormal.IUT.XiFPaper.S730QVFamBlockLatticeAlignmentActual
open LeanFormal.IUT.XiFPaper.S741QVFamBlockSMulActual
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
/-- Pure-tensor image statement: tprod of local fractional-lattice elements
maps into the local fractional lattice of the total exponent. -/
def PureTensorFractionalLatticeImage : Prop :=
  ∀ (f : (i : qVFamTensorV) →
      CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i))),
    (∀ i, f i ∈ padicFractionalLattice (p := qVFamTensorP T b)
      (K := CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i)))
        (c i)) →
    (qVFamBlockLinearEquiv (l := l) T b
      (finitePadicTensorTprod (p := qVFamTensorP T b)
        (fun i => CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i))) f) :
      rootBase T b) ∈ padicFractionalLattice (p := qVFamTensorP T b)
        (K := rootBase T b) (∑ i, c i)
/-- Span induction: pure-tensor image implies the full lattice image. -/
theorem qVFamBlockMapsFractionalLattice_of_pure
    (hpure : PureTensorFractionalLatticeImage (l := l) T b c) :
    QVFamBlockMapsFractionalLattice (l := l) T b c := by
  intro x hx
  change x ∈ Submodule.span ℤ_[qVFamTensorP T b]
    (tensorIntegralRegion (p := qVFamTensorP T b)
      (fun i => CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i)))
      (fun i => (padicFractionalLattice (p := qVFamTensorP T b)
        (K := CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i)))
          (c i) : Set _))) at hx
  refine Submodule.span_induction (p :=
    fun x => (qVFamBlockLinearEquiv (l := l) T b x : rootBase T b) ∈
      padicFractionalLattice (p := qVFamTensorP T b) (K := rootBase T b) (∑ i, c i))
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨f, hf, rfl⟩
    exact hpure (fun i => f i) (fun i => (f i).2)
  · exact (padicFractionalLattice (p := qVFamTensorP T b)
      (K := rootBase T b) (∑ i, c i)).zero_mem
  · intro x y hx hy
    exact add_mem hx hy
  · intro z x hx
    rw [show qVFamBlockLinearEquiv (l := l) T b (z • x) =
        z • qVFamBlockLinearEquiv (l := l) T b x from
      qVFamBlockSMulCompatibility_actual (l := l) T b z x]
    exact Submodule.smul_mem _ z hx
/-- Exact local norm bound from the image containment, no isometry. -/
theorem image_norm_bound_of_maps
    (hmaps : QVFamBlockMapsFractionalLattice (l := l) T b c) :
    ∀ x ∈ arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
      qVFamTensorTuple c,
      ‖(qVFamBlockLinearEquiv (l := l) T b x : rootBase T b)‖ ≤
        Real.rpow (qVFamTensorP T b : Real) (-(∑ i, c i)) := by
  intro x hx
  rw [← mem_padicFractionalLattice_iff]
  exact hmaps x hx
/-- Exact remaining pure-tensor goal. -/
def S772PureTensorGoal : Prop :=
  PureTensorFractionalLatticeImage (l := l) T b c
end LeanFormal.IUT.XiFPaper.S772QVFamBlockMapsLatticeActual
