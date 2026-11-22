import tmp.sheaf.xif.paper.S1074SupplyCNormOrderActual

/-! # S1078: qVFamNormalizedCoefficient = order iff e = 1

S826 gives the exact factor c_norm = order/e under the normalized norm
compatibility.  Hence c_norm = order iff e = 1, and c_norm ≠ order for e ≠ 1.
The norm card NormalizedCompletionNormValuationFormula is still not proved, and
no witness e ≠ 1 is constructed; this file records both exact directions and the
exact counterexample obligation. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1078CNormOrderIffActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S826CNormOrderRamificationActual
open LeanFormal.IUT.XiFPaper.S1074SupplyCNormOrderActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (e : Real) (hepos : 0 < e)
variable (hcomp : QVFamNormalizedNormCompatibility (l := l) T b e)

/-- Exact iff: Supply c_norm = order iff e = 1, under the norm compatibility. -/
theorem s1078SupplyCNorm_eq_order_iff_e_one :
    S1074SupplyCNormEqOrder (l := l) T b ↔ e = 1 :=
  qVFamNormalizedCoefficient_eq_order_iff_e_eq_one (l := l) T b e hepos hcomp

/-- For e ≠ 1, Supply c_norm is not the order: exact negative direction. -/
theorem s1078SupplyCNorm_ne_order_of_e_ne_one (he : e ≠ 1) :
    ¬ S1074SupplyCNormEqOrder (l := l) T b :=
  qVFamNormalizedCoefficient_ne_order_of_e_ne_one (l := l) T b e hepos hcomp he

/-- Exact counterexample obligation for e ≠ 1: a positive e ≠ 1 satisfying the
normalized norm compatibility.  No inhabitant is asserted. -/
def S1078EneOneCounterexampleRequired : Prop :=
  ∃ e : Real, 0 < e ∧ e ≠ 1 ∧
    QVFamNormalizedNormCompatibility (l := l) T b e

/-- Exact minimal input for Supply c_norm = order is the e = 1 norm
compatibility (or the S827 card + ramification alignment + e = 1). -/
def S1078ExactMinimal : Prop :=
  S1074NormCompatibilityOne (l := l) T b

end LeanFormal.IUT.XiFPaper.S1078CNormOrderIffActual
end