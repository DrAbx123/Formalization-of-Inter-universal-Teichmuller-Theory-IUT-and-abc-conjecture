import tmp.sheaf.xif.paper.S3131CoefficientReductionActual
import tmp.sheaf.xif.paper.S3131QCLeHCComparisonActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36LocalIdealValuation

/-! # S3131 task-34 / R2: (iii-b) PROVED, (iii-a) reduced to Mathlib identity

(iii-b) PROVED: classical completion valuation exponent of the actual normalized
qVFamily generator = actual qVFamily discrete exponent (Example36 exponent
= -WithZero.log o Valued.v; qVFamily exponent = -Multiplicative.toAdd o
WithZero.unzero o Valued.v; WithZero.exp/log bridge).
(iii-a) REDUCED and the tree-specific half CLOSED: qVFamTensorP = natGenerator of
the rational place (rfl, by Rat.HeightOneSpectrum.primesEquiv.toFun = natGenerator);
hence S3131RationalPlaceAbsNormMissing <-> the single Mathlib-level identity
absNorm P.asIdeal = natGenerator P for P = comap(qVFamTensorPlace).  Source IUT III
Rem 3.1.1(ii) p-adic normalization (corpus 5408-5465).
No sorry/axiom/True/PUnit. -/

noncomputable section
open scoped BigOperators WithZero Valued
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3131R2ReductionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- **(iii-b) PROVED.**  Valuation exponent of the normalized generator equals
the actual qVFamily discrete exponent. -/
theorem S3131Nu_qVFamNormalizedGenerator_eq_exponent :
    completionValuationExponent (qVFamTensorPlace (l := l) T b).maximalIdeal
      (Units.mk0 (qVFamNormalizedGenerator (l := l) T b)
        (qVFamNormalizedGenerator_ne_zero (l := l) T b))
      = (qVFamily T b).exponent := by
  rw [completionValuationExponent_eq_neg_log]
  have hq : Valued.v ((qVFamily T b).q :
      Completion (qVFamTensorPlace (l := l) T b)) ≠ 0 :=
    (qVFamily T b).valuation_ne_zero
  have hval : ((qVFamNormalizedGenerator (l := l) T b :
      NormalizedCompletion (qVFamTensorPlace (l := l) T b)))
      = ((qVFamily T b).q : Completion (qVFamTensorPlace (l := l) T b)) :=
    rfl
  have hunit : Units.mk0 (qVFamNormalizedGenerator (l := l) T b)
        (qVFamNormalizedGenerator_ne_zero (l := l) T b)
      = Units.mk0 ((qVFamily T b).q : Completion (qVFamTensorPlace (l := l) T b)) hq := by
    ext
    exact hval
  rw [hunit]
  unfold FinitePlaceQCandidate.exponent
  congr 1
  have h1 : WithZero.exp (Multiplicative.toAdd (WithZero.unzero hq)) =
      Valued.v ((qVFamily T b).q : Completion (qVFamTensorPlace (l := l) T b)) := by
    unfold WithZero.exp
    rw [Multiplicative.ofAdd_toAdd, WithZero.coe_unzero hq]
  rw [← h1, WithZero.log_exp]

/-- **(iii-a) tree-specific half CLOSED.**  The rational-prime norm base of the
native tensor place is the natGenerator of its contracted rational place. -/
theorem S3131QVFamTensorP_eq_natGenerator :
    qVFamTensorP (l := l) T b =
      Rat.HeightOneSpectrum.natGenerator
        ((comap (k := ℚ) (qVFamTensorPlace (l := l) T b)).maximalIdeal) := rfl

/-- **(iii-a) EXACT RESIDUAL.** -/
def S3131RationalPlaceAbsNormMissing : Prop :=
  (Ideal.absNorm (comap (k := ℚ) (qVFamTensorPlace (l := l) T b)).maximalIdeal.asIdeal
    : ℝ) = (qVFamTensorP (l := l) T b : ℝ)

/-- **(iii-a) REDUCTION.**  The tree-specific condition is equivalent to the
single Mathlib-level identity absNorm(asIdeal) = natGenerator. -/
theorem S3131RationalPlaceAbsNorm_reduction :
    S3131RationalPlaceAbsNormMissing (l := l) T b ↔
      Ideal.absNorm (comap (k := ℚ) (qVFamTensorPlace (l := l) T b)).maximalIdeal.asIdeal
        = Rat.HeightOneSpectrum.natGenerator
          ((comap (k := ℚ) (qVFamTensorPlace (l := l) T b)).maximalIdeal) := by
  unfold S3131RationalPlaceAbsNormMissing
  rw [S3131QVFamTensorP_eq_natGenerator]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

#check S3131Nu_qVFamNormalizedGenerator_eq_exponent
#check S3131QVFamTensorP_eq_natGenerator
#check S3131RationalPlaceAbsNorm_reduction

end LeanFormal.IUT.XiFPaper.S3131R2ReductionActual

end
