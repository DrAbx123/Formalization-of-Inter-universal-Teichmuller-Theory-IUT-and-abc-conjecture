import tmp.sheaf.xif.paper.S826CNormOrderRamificationActual
import tmp.sheaf.xif.paper.S827PaperValueGroupNormCardActual

/-! # S1074: Supply c_norm = order via the norm bridge / e = 1

S826 gives the exact ramification formula c_norm = order / e under the
normalized norm compatibility.  Hence Supply c_norm = order iff e = 1.
S827 reduces the norm-card to the frozen NormalizedCompletionNormValuationFormula
plus the ramification alignment.  Neither the card nor e = 1 is proved; this
file records the exact minimal data, no fake formula and no unconditional
Supply c_norm = order. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1074SupplyCNormOrderActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S826CNormOrderRamificationActual
open LeanFormal.IUT.XiFPaper.S827PaperValueGroupNormCardActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Target: the supply-version normalized coefficient equals the qVFamily order. -/
def S1074SupplyCNormEqOrder : Prop :=
  qVFamNormalizedCoefficient T b = ((qVFamily T b).order : Real)

/-- Exact norm compatibility at e = 1. -/
def S1074NormCompatibilityOne : Prop :=
  QVFamNormalizedNormCompatibility (l := l) T b 1

/-- If the normalized norm compatibility holds at e = 1, the supply
coefficient is the order. -/
theorem s1074SupplyCNorm_eq_order_of_normCompatibilityOne
    (h : S1074NormCompatibilityOne (l := l) T b) :
    S1074SupplyCNormEqOrder (l := l) T b := by
  unfold S1074SupplyCNormEqOrder S1074NormCompatibilityOne at *
  rw [qVFamNormalizedCoefficient_eq_order_div_e (l := l) T b 1 h]
  norm_num

/-- Exact card input from S827: frozen norm card + ramification alignment. -/
def S1074CardInput : Prop :=
  Nonempty (PaperValueGroupNormData (l := l) T b)

/-- Exact e = 1 condition (relative ramification index one). -/
def S1074EOne : Prop :=
  relativeRamificationIndex (k := ℚ) (paperValueGroupPlace (l := l) T b) = 1

/-- Exact minimal data for Supply c_norm = order: S827 card data + e = 1, or
directly the e = 1 norm compatibility.  No inhabitant is asserted. -/
def S1074ExactMinimal : Prop :=
  S1074CardInput (l := l) T b ∧ S1074EOne (l := l) T b

end LeanFormal.IUT.XiFPaper.S1074SupplyCNormOrderActual
end