import tmp.sheaf.xif.paper.S720OneFactorTensorNormReductionActual
import LeanFormal.IUT.Foundations.LocalFields.PadicFractionalLattice

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S724QVFamBlockFractionalLatticeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S720OneFactorTensorNormReductionActual
open LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.LocalFieldLogarithm
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
variable (c : qVFamTensorV → Real)

/-- The one-factor tensor equivalence sends a pure tensor to its coordinate. -/
theorem qVFamBlockLinearEquiv_tprod
    (f : (i : qVFamTensorV) →
      CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i))) :
    qVFamBlockLinearEquiv (l := l) T b
        (finitePadicTensorTprod (p := qVFamTensorP T b)
          (fun i => CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i))) f) =
      f () := by
  unfold qVFamBlockLinearEquiv
  change (PiTensorProduct.subsingletonEquiv ())
      (PiTensorProduct.tprod ℚ_[qVFamTensorP T b] f) = f ()
  rw [PiTensorProduct.subsingletonEquiv_apply_tprod]

/-- Exact target: the tensor fractional lattice maps into the local padic
fractional lattice of the total exponent sum.  No inhabitant is asserted. -/
def QVFamBlockMapsFractionalLatticeGoal : Prop :=
  QVFamBlockMapsFractionalLattice (l := l) T b c

/-- Exact goal package. -/
def S724ExactGoal : Prop :=
  QVFamBlockMapsFractionalLatticeGoal (l := l) T b c

end LeanFormal.IUT.XiFPaper.S724QVFamBlockFractionalLatticeActual

end
