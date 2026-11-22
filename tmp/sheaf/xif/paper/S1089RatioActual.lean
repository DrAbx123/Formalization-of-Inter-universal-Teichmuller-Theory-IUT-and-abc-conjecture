import tmp.sheaf.xif.paper.S1088CoeffLeActual
import tmp.sheaf.xif.paper.S118QVFamNormRatioValueActual
/-! # S1089: residue-ratio >= 1 from the base-p power form
If residueNormBase(qVFamTensorPlace) = p^f with f>=1, then
log(residueNormBase)/log p = f >= 1.  The base-p power form is the exact
remaining arithmetic input; f is the actual local residue degree. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000
namespace LeanFormal.IUT.XiFPaper.S1089RatioActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataGapActual
open LeanFormal.IUT.XiFPaper.S1088CoeffLeActual
open LeanFormal.IUT.XiFPaper.S118QVFamNormRatioValueActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
/-- Exact base-p power form of the qVFam residue norm. -/
def S1089BasePow (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Prop :=
  residueNormBase (qVFamTensorPlace T b) =
    (qVFamTensorP T b : Real) ^
      localResidueDegree (k := ℚ) (qVFamTensorPlace T b)
theorem s1089Ratio_of_basePow
    (hbase : S1089BasePow (l := l) T b) :
    S1088RatioGeOne (l := l) T b := by
  unfold S1088RatioGeOne
  rw [hbase, Real.log_pow]
  have hp1 : (1 : Real) < (qVFamTensorP T b : Real) := by
    have hprime : Nat.Prime (qVFamTensorP T b) := Fact.out
    exact_mod_cast hprime.one_lt
  have hlogp : 0 < Real.log (qVFamTensorP T b : Real) := Real.log_pos hp1
  have hf : (1 : Nat) ≤ localResidueDegree (k := ℚ) (qVFamTensorPlace T b) :=
    Nat.succ_le_of_lt (localResidueDegree_pos (k := ℚ) (qVFamTensorPlace T b))
  rw [mul_div_cancel_right₀ _ hlogp.ne']
  exact_mod_cast hf
end LeanFormal.IUT.XiFPaper.S1089RatioActual
