/-
INVALID AS PAPER OBJECT (completion 2l-th root audit).

This file depends on a completion 2l-th root q_v^(1/2l) of the qVFamily q
(PaperQRootCard / NatRootSystem (qVUnit ...) / HalfRootInCompletion).
S342QVFamilyRootImpossibleActual proves that this is impossible: the order is
coprime to l while a 2l-th root forces 2l | order.  The conditional records
and consequences below are retained only as invalidated history; they must not
be used as paper objects or as inputs to further constructions.
-/
import tmp.sheaf.xif.paper.BadPlaceHalfRootSupplyActual
import Mathlib.NumberTheory.Padics.PadicNumbers

/-! # Half-root existence criterion

HalfRootInCompletion is exactly a completion unit r with r^(2l) equal to the
qVFamily normalized generator and with the prescribed normalized norm.  This
file records the exact existential criterion and gives an actual valuation
counterexample in Q_5: the element 5 has no 2l-th root, because its valuation
is not divisible by 2l.  This is the obstruction behind the missing completion
root API; no fake root is constructed.

No sorry/axiom/True/PUnit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.BadPlaceHalfRootCriterionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperConstantsActual
open LeanFormal.IUT.XiFPaper.BadPlaceNormalizationSourceActual
open LeanFormal.IUT.XiFPaper.BadPlaceRootHullScalingFormulaActual
open LeanFormal.IUT.XiFPaper.PaperBadPlaceTensorGeometryActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlaceHalfRootSupplyActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Exact existential criterion for the half-root datum. -/
theorem HalfRootInCompletion_iff_exists :
    Nonempty (HalfRootInCompletion T b) ↔
      ∃ r : (CommonPrimeCompletion (halfRootPlace T b))ˣ,
        r ^ (2 * l.value) = qVFamNormalizedGenerator T b ∧
          ‖(r : CommonPrimeCompletion (halfRootPlace T b))‖ =
            (qVFamTensorP T b : Real) ^
              (-(QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b /
                (2 * l.value : Real))) := by
  constructor
  · rintro ⟨R⟩
    exact ⟨R.root, R.pow_twoL, R.norm_eq⟩
  · rintro ⟨r, hpow, hnorm⟩
    exact ⟨⟨r, hpow, hnorm⟩⟩

/-- If a half-root exists, its norm power is the qVFamily generator norm. -/
theorem halfRoot_norm_pow_of_exists
    (h : Nonempty (HalfRootInCompletion T b)) :
    ∃ r : (CommonPrimeCompletion (halfRootPlace T b))ˣ,
      ‖(r : CommonPrimeCompletion (halfRootPlace T b))‖ ^ (2 * l.value) =
        (qVFamTensorP T b : Real) ^
          (-(QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b)) := by
  rcases h with ⟨R⟩
  refine ⟨R.root, ?_⟩
  rw [R.norm_eq]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- Actual valuation counterexample: 5 has no 2l-th root in Q_5 for l >= 5. -/
theorem padic_five_no_twoL_root (l : PrimeGeFive) :
    ¬ ∃ r : ℚ_[5], r ^ (2 * l.value) = (5 : ℚ_[5]) := by
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rintro ⟨r, hr⟩
  have h2l : 0 < 2 * l.value := by
    have : 0 < l.value := l.prime.pos
    omega
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, zero_pow h2l.ne'] at hr
    norm_num at hr
  have hnorm := congrArg norm hr
  rw [norm_pow, Padic.norm_p] at hnorm
  rw [Padic.norm_eq_zpow_neg_valuation hr0] at hnorm
  have hpow : ((5 : ℝ) ^ (-r.valuation)) ^ (2 * l.value) =
      (5 : ℝ) ^ ((-r.valuation) * (2 * l.value : ℤ)) := by
    rw [← zpow_natCast, ← zpow_mul]
  rw [hpow] at hnorm
  have hnorm' : (5 : ℝ) ^ ((-r.valuation) * (2 * l.value : ℤ)) =
      (5 : ℝ) ^ (-1 : ℤ) := by
    simpa using hnorm
  have hexp := (zpow_right_inj₀ (a := (5 : ℝ)) (by norm_num) (by norm_num)).mp hnorm'
  have hprod : r.valuation * (2 * l.value : ℤ) = 1 := by linarith
  have hdvd : (2 * l.value : ℤ) ∣ 1 := ⟨r.valuation, by simpa [mul_comm] using hprod⟩
  have hle : (2 * l.value : ℤ) ≤ 1 := by
    have h := Int.natAbs_le_of_dvd_ne_zero hdvd (by norm_num : (1 : ℤ) ≠ 0)
    rw [Int.natAbs_ofNat, Int.natAbs_ofNat] at h
    exact_mod_cast h
  have hge : (10 : ℤ) ≤ 2 * l.value := by
    have h5 : (5 : ℤ) ≤ l.value := by exact_mod_cast l.ge_five
    omega
  omega

end LeanFormal.IUT.XiFPaper.BadPlaceHalfRootCriterionActual
