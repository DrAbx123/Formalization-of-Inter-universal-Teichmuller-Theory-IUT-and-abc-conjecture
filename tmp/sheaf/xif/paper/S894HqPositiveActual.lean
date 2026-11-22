import tmp.sheaf.xif.paper.S888HqHthetaActual
import tmp.sheaf.xif.paper.S817StackRootUnitNormActual
import tmp.sheaf.xif.paper.S825StackFactorCNormEquivActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S894HqPositiveActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S888HqHthetaActual
open LeanFormal.IUT.XiFPaper.S817StackRootUnitNormActual
open LeanFormal.IUT.XiFPaper.S820FiniteLScalingGeneratorActual
open LeanFormal.IUT.XiFPaper.S825StackFactorCNormEquivActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Direct positive Hq: if every c_norm equals the paper order, each weighted
term vanishes; no weight nonneg condition is used. -/
theorem hqWeightedCNormOrder_of_cNorm_eq_order
    (h : ∀ b : Bad (nativePlaceSelection T),
      qVFamNormalizedCoefficient (l := l) T b = ((qVFamily T b).order : Real)) :
    HqWeightedCNormOrder (l := l) T := by
  unfold HqWeightedCNormOrder
  apply Finset.sum_eq_zero
  intro b hb
  rw [h b]
  ring

/-- Pointwise weighted term vanishing from c_norm = order. -/
theorem hq_weighted_term_eq_zero_of_cNorm_eq_order
    (h : ∀ b : Bad (nativePlaceSelection T),
      qVFamNormalizedCoefficient (l := l) T b = ((qVFamily T b).order : Real))
    (b : Bad (nativePlaceSelection T)) :
    nativeBadLocalWeight T b *
      ((qVFamNormalizedCoefficient (l := l) T b -
        ((qVFamily T b).order : Real)) *
        Real.log (qVFamTensorP T b : Real)) = 0 := by
  rw [h b]
  ring

/-- Connect the S825 actual stack factor: if all stack root unit factors are
one, Hq is zero. -/
theorem hqWeightedCNormOrder_of_stackRootUnitFactorOne
    (h : ∀ b : Bad (nativePlaceSelection T),
      StackRootUnitFactorOne T b) :
    HqWeightedCNormOrder (l := l) T := by
  apply hqWeightedCNormOrder_of_cNorm_eq_order (l := l) T
  intro b
  exact (StackRootUnitFactorOne_iff_cNorm_eq_order T b).mp (h b)

/-- Equivalent direct form via the per-b S825/S817 factor equality. -/
theorem hqWeightedCNormOrder_of_all_stackRootFactor_eq_one
    (h : ∀ b : Bad (nativePlaceSelection T), ∀ i : qVFamTensorV,
      stackRootUnitFactor (l := l) T b i = 1) :
    HqWeightedCNormOrder (l := l) T := by
  apply hqWeightedCNormOrder_of_stackRootUnitFactorOne (l := l) T
  intro b
  exact h b

/-- Exact remaining condition; no inhabitant is asserted. -/
def S894HqWeightedCNormOrderRequired : Prop :=
  HqWeightedCNormOrder (l := l) T

end LeanFormal.IUT.XiFPaper.S894HqPositiveActual

end
