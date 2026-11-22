import tmp.sheaf.xif.paper.S1526S1087CoeffLeActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1547ResidueNormBaseActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S1526S1087CoeffLeActual
open LeanFormal.IUT.XiFPaper.S1087Q1UContainmentActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Exact first missing number-theory lemma: the residue norm base at the
rational place below the actual F-place is the rational prime qVFamTensorP. -/
def S1547ResidueNormBaseEqPrime : Prop :=
  residueNormBase (comap (k := ℚ) (qVFamTensorPlace T b)) =
    (qVFamTensorP T b : Real)

/-- Conditional reduction: the residue-norm-base equality gives the base log
ratio at least one. -/
theorem s1547ResidueLogRatio_of_residueNormBase
    (h : S1547ResidueNormBaseEqPrime (l := l) T b) :
    S1526ResidueLogRatioGeOne (l := l) T b := by
  unfold S1526ResidueLogRatioGeOne S1547ResidueNormBaseEqPrime at *
  rw [residueNormBase_eq_lower_pow (k := ℚ) (qVFamTensorPlace T b), h,
    Real.log_pow]
  have hlog : Real.log (qVFamTensorP T b : Real) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos
    · exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).ne_one
  rw [mul_div_cancel_right₀ _ hlog]
  exact_mod_cast localResidueDegree_pos (k := ℚ) (qVFamTensorPlace T b)

/-- Conditional S1087CoeffLe from the residue-norm-base equality. -/
theorem s1547CoeffLe_of_residueNormBase
    (h : S1547ResidueNormBaseEqPrime (l := l) T b) :
    S1087CoeffLe (l := l) T b :=
  s1526CoeffLe_of_residueLogRatio T b
    (s1547ResidueLogRatio_of_residueNormBase (l := l) T b h)

/-- The exact first missing number-theory lemma as a named type. -/
abbrev S1547ExactFirstLemma : Prop := S1547ResidueNormBaseEqPrime (l := l) T b

end LeanFormal.IUT.XiFPaper.S1547ResidueNormBaseActual

end
