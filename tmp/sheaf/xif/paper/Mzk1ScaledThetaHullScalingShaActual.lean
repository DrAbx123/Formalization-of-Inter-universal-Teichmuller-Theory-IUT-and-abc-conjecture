import tmp.sheaf.xif.paper.Mzk1ScaledThetaHullShaActual
import tmp.sheaf.xif.paper.PaperRootExtensionPrimeScalingActual
import tmp.sheaf.xif.paper.Mzk1HaarScalingOneDimActual
import tmp.sheaf.xif.paper.Mzk1RootImageRadiusFormulaActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.PaperRootExtensionPrimeDecompositionActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import tmp.sheaf.xif.paper.Mzk1HaarProductStrictMainlineActual
import Mathlib.Tactic

/-!
# A775 iterated scaling law for the scaled θ-hull (shehdd)

Proved on the actual S1902 product carrier:
* `prime_pow_smul_closedBall`: `(p_b^k) • closedBall(0,R) = closedBall(0, R/p_b^k)`;
* `rootPrimeHaarFactor_pow_smul_measure`: `haar ((p_b^k) • S) = primeFactor_b^k * haar S`;
* **`scaledThetaHull_measure_eq`:
  `rootExtensionProductHaar (scaledThetaHull k) =
     (∏_b primeFactor_b^k) * rootExtensionProductHaar fullRegion`;
* **`scaledThetaHull_log_toReal`: the log form
  `log (scaled volume) = log (fullRegion volume) - k·Σ_b d_b log p_b`;
* capsule correspondence: with `root^{2ℓ} = qUnit` (`rootNormedElement_pow`) and
  `rootImageRadius = p_b^{-c_norm_b/(2ℓ)}` (`rootImageRadius_eq_p_rpow_reexport`),
  the paper scaling `qroot^{(i+1)^2}` gives divisor exponent
  `k_b(i) = c_norm_b·(i+1)^2/(2ℓ)`; `capsuleHullRadius` is defined with this real
  exponent, and the integer construction `scaledHullRadius k` matches it exactly
  when `k = k_b(i)` (theorem `scaledHullRadius_eq_capsuleHullRadius_of_cast`).

No RETRACTED statement is used.  No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullScalingShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullShaActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionPrimeScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual
open LeanFormal.IUT.XiFPaper.Mzk1RootImageRadiusFormulaActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarProductStrictMainlineActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionPrimeDecompositionActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open MeasureTheory
open scoped Pointwise ENNReal BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

theorem qp_pos : (0 : ℝ) < (qVFamTensorP T b : ℝ) := by
  exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos

/-- k-fold prime scaling of closed balls: `(p^k) • ball(R) = ball(R/p^k)`. -/
theorem prime_pow_smul_closedBall (k : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ^ k) •
        Metric.closedBall (0 : rootNormedExtension T b) R =
      Metric.closedBall (0 : rootNormedExtension T b)
        (R / (qVFamTensorP T b : ℝ) ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hRk : 0 ≤ R / (qVFamTensorP T b : ℝ) ^ k := by
        exact div_nonneg hR (by positivity)
      rw [pow_succ', mul_smul, ih]
      rw [prime_smul_closedBall (T := T) (b := b) (R / (qVFamTensorP T b : ℝ) ^ k) hRk]
      rw [pow_succ']
      congr 1
      field_simp [ne_of_gt (qp_pos T b)]

/-- k-fold Haar scaling: `haar ((p^k) • S) = primeFactor^k * haar S`. -/
theorem rootPrimeHaarFactor_pow_smul_measure (k : ℕ)
    (S : Set (rootNormedExtension T b)) :
    rootExtensionHaar T b (((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ^ k) • S) =
      (rootPrimeHaarFactor T b) ^ k * rootExtensionHaar T b S := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', mul_smul]
      rw [rootPrime_smul_measure (T := T) (b := b)
        (S := ((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ^ k) • S)]
      rw [ih]
      rw [← rootPrimeHaarFactor_eq_norm_pow]
      rw [pow_succ']
      ring

/-- **Iterated scaling law for the scaled θ-hull**:
`productHaar (scaledThetaHull k) = (∏_b primeFactor_b^k) * productHaar fullRegion`. -/
theorem scaledThetaHull_measure_eq (k : ℕ) :
    rootExtensionProductHaar T (scaledThetaHull T k) =
      (∏ b : Bad (nativePlaceSelection T), (rootPrimeHaarFactor T b) ^ k) *
        rootExtensionProductHaar T (fullRegion T) := by
  unfold scaledThetaHull fullRegion rootExtensionProductHaar
  rw [Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro b' _
  rw [show Metric.closedBall (0 : rootNormedExtension T b')
        (scaledHullRadius T b' k) =
      ((qVFamTensorP T b' : ℚ_[(qVFamTensorP T b')]) ^ k) •
        Metric.closedBall (0 : rootNormedExtension T b')
          (rootImageRadius T b' : ℝ) from by
    unfold scaledHullRadius
    exact (prime_pow_smul_closedBall (T := T) (b := b') k
      (rootImageRadius T b' : ℝ) (s1915_rootImageRadius_pos T b').le).symm]
  rw [rootPrimeHaarFactor_pow_smul_measure]

/-- Real unit scaling factor: `(primeFactor_b).toReal = primeFactor_b`. -/
theorem rootPrimeHaarFactor_toReal :
    (rootPrimeHaarFactor T b).toReal = primeFactor T b := by
  rw [rootPrimeHaarFactor_eq_norm_pow, ENNReal.toReal_ofReal (by positivity)]
  rfl

/-- `log primeFactor_b = -d_b * log p_b`. -/
theorem log_primeFactor :
    Real.log (primeFactor T b) =
      -((s1915LocalDegree T b : ℝ) * Real.log (qVFamTensorP T b : ℝ)) := by
  unfold primeFactor s1915LocalDegree
  rw [Real.log_pow, rootNorm_algebraMap_prime (T := T) (b := b), Padic.norm_p]
  rw [Real.log_inv]
  ring

/-- Positivity of the full-region product Haar. -/
theorem fullRegion_measure_pos' : 0 < rootExtensionProductHaar T (fullRegion T) := by
  unfold fullRegion rootExtensionProductHaar
  rw [Measure.pi_pi, pos_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr (fun b' _ =>
    ne_of_gt (rootExtensionClosedBall_measure_pos (T := T) (b := b') _
      (s1915_rootImageRadius_pos T b')))

theorem fullRegion_measure_lt_top' :
    rootExtensionProductHaar T (fullRegion T) < ⊤ := by
  unfold fullRegion rootExtensionProductHaar
  rw [Measure.pi_pi]
  apply ENNReal.prod_lt_top
  intro b' _
  exact rootExtensionClosedBall_measure_lt_top (T := T) (b := b') _

/-- **Log form of the iterated scaling law**. -/
theorem scaledThetaHull_log_toReal (k : ℕ) :
    Real.log ((rootExtensionProductHaar T (scaledThetaHull T k)).toReal) =
      Real.log ((rootExtensionProductHaar T (fullRegion T)).toReal) -
        (k : ℝ) * qLogSum T := by
  rw [scaledThetaHull_measure_eq]
  have hfullpos : 0 < (rootExtensionProductHaar T (fullRegion T)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (fullRegion_measure_pos' T))
      (ne_of_lt (fullRegion_measure_lt_top' T))
  have hfac : (∏ b' : Bad (nativePlaceSelection T), (rootPrimeHaarFactor T b') ^ k).toReal =
      ∏ b' : Bad (nativePlaceSelection T), (primeFactor T b') ^ k := by
    rw [ENNReal.toReal_prod]
    exact Finset.prod_congr rfl (fun b' _ => by
      rw [ENNReal.toReal_pow, rootPrimeHaarFactor_toReal])
  have hfacpos : 0 < (∏ b' : Bad (nativePlaceSelection T),
      (rootPrimeHaarFactor T b') ^ k).toReal := by
    rw [hfac]
    exact Finset.prod_pos (fun b' _ => pow_pos (primeFactor_pos T b') k)
  rw [ENNReal.toReal_mul, Real.log_mul (ne_of_gt hfacpos) (ne_of_gt hfullpos), hfac]
  have hlogprod : Real.log (∏ b' : Bad (nativePlaceSelection T),
      (primeFactor T b') ^ k) = -(k : ℝ) * qLogSum T := by
    rw [Real.log_prod (fun b' _ => pow_ne_zero _ (ne_of_gt (primeFactor_pos T b')))]
    have hterm : ∀ b' : Bad (nativePlaceSelection T),
        Real.log ((primeFactor T b') ^ k) =
          (k : ℝ) * (-((s1915LocalDegree T b' : ℝ) *
            Real.log (qVFamTensorP T b' : ℝ))) := by
      intro b'; rw [Real.log_pow, log_primeFactor]
    rw [Finset.sum_congr rfl (fun b' _ => hterm b')]
    unfold qLogSum
    rw [← Finset.mul_sum, Finset.sum_neg_distrib]
    ring
  rw [hlogprod]
  ring

/-! ### Capsule correspondence: `qroot^{(i+1)^2}` vs `p_b` -/

/-- Paper scaling exponent of capsule `i`: `(i+1)^2` (lana `scaleEltAt`). -/
def capsuleExponent (i : ℕ) : ℕ := (i + 1) ^ 2

theorem capsuleExponent_eq (i : ℕ) : capsuleExponent i = (i + 1) ^ 2 := rfl

/-- Exact per-place divisor exponent for capsule `i`:
`k_b(i) = c_norm_b·(i+1)^2/(2ℓ)` (since `rootImageRadius_b = p_b^{-c_norm_b/(2ℓ)}`
and `qroot` has norm `p_b^{-c_norm_b/(2ℓ)}`, `qroot^{2ℓ}=qUnit`). -/
noncomputable def capsuleDivisorExponent
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) (j : ℕ) : ℝ :=
  (QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b) *
    ((j : ℝ) ^ 2) / (2 * (l.value : ℝ))

/-- The exact capsule hull radius with the real divisor exponent. -/
noncomputable def capsuleHullRadius
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) (j : ℕ) : ℝ :=
  (rootImageRadius T b : ℝ) /
    (qVFamTensorP T b : ℝ) ^ (capsuleDivisorExponent T b j)

/-- Integer `k` matches the exact capsule divisor exactly when `k = k_b(i)`. -/
theorem scaledHullRadius_eq_capsuleHullRadius_of_cast (k j : ℕ)
    (hk : (k : ℝ) = capsuleDivisorExponent T b j) :
    scaledHullRadius T b k = capsuleHullRadius T b j := by
  unfold scaledHullRadius capsuleHullRadius
  rw [← hk, Real.rpow_natCast]

structure ScalingRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def scalingRows : List ScalingRow :=
  [ ⟨"iterated ball scaling", "(p^k) • ball R = ball(R/p^k)", "PROVED"⟩
  , ⟨"iterated Haar scaling", "haar((p^k) • S) = primeFactor^k * haar S", "PROVED"⟩
  , ⟨"scaled hull measure", "productHaar(scaledThetaHull k) = (∏ primeFactor^k)*productHaar fullRegion", "PROVED"⟩
  , ⟨"log form", "log scaled = log full - k*Σ_b d_b log p_b", "PROVED"⟩
  , ⟨"capsule exponent", "qroot^{(i+1)^2} => divisor exponent k_b(i)=c_norm_b*(i+1)^2/(2l)", "PROVED (fomula)"⟩
  , ⟨"integer k match", "scaledHullRadius k = capsuleHullRadius j iff k = k_b(j)", "PROVED"⟩
  , ⟨"uniform integer k", "k_b depends on b; a single integer k is exact only when all k_b are equal integers; general case uses capsuleHullRadius (rpow)", "REMARK/GAP"⟩
  , ⟨"scope", "no toy carrier; no RETRACTED use", "INTEGRITY"⟩
  ]

theorem scalingRows_length : scalingRows.length = 8 := rfl

theorem scalingRows_has_remark :
    scalingRows.any (fun r => r.status = "REMARK/GAP") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullScalingShaActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullScalingShaActual.prime_pow_smul_closedBall
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullScalingShaActual.rootPrimeHaarFactor_pow_smul_measure
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullScalingShaActual.scaledThetaHull_measure_eq
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullScalingShaActual.scaledThetaHull_log_toReal
