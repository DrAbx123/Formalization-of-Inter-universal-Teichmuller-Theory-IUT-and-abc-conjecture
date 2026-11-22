import tmp.sheaf.xif.paper.S803RootNormCarrierDecisionActual
import tmp.sheaf.xif.paper.S720OneFactorTensorNormReductionActual

/-! # S807: norm bound on the RootNormQVBlock fractional lattice

The new carrier norm is the rootBase norm of the transferred block.  The
local fractional-lattice norm lemma therefore gives, for every coefficient
family c, the actual bound

  ||x|| <= p^(-sum_i c_i),  x in RootNormTensorFractionalLattice c,

conditional only on the one-factor lattice map
`QVFamBlockMapsFractionalLattice c`.  No old qVFamTensorBlock norm
preservation and no completion root are used.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S807RootNormLatticeBoundActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S717TensorLatticeNormExactActual
open LeanFormal.IUT.XiFPaper.S720OneFactorTensorNormReductionActual
open LeanFormal.IUT.XiFPaper.S771RootNormCarrierActual
open LeanFormal.IUT.XiFPaper.S784RootNormRegionsActual
open LeanFormal.IUT.XiFPaper.S803RootNormCarrierDecisionActual
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

theorem rootNormTensorLatticeNormLe_of_maps
    (hmap : QVFamBlockMapsFractionalLattice (l := l) T b c) :
    RootNormTensorLatticeNormLe (l := l) T b c
      (Real.rpow (qVFamTensorP T b : Real) (-(∑ i, c i))) := by
  intro x hx
  rw [rootNormCarrier_norm_eq]
  exact padicFractionalLattice_norm_le (l := l) T b (∑ i, c i)
    (hmap x.toBlock hx)

theorem S803RootNormLatticeBoundRequired_of_maps
    (hmap : QVFamBlockMapsFractionalLattice (l := l) T b c) :
    S803RootNormLatticeBoundRequired (l := l) T b c
      (Real.rpow (qVFamTensorP T b : Real) (-(∑ i, c i))) := by
  unfold S803RootNormLatticeBoundRequired
  exact rootNormTensorLatticeNormLe_of_maps (l := l) T b c hmap

end LeanFormal.IUT.XiFPaper.S807RootNormLatticeBoundActual

end
