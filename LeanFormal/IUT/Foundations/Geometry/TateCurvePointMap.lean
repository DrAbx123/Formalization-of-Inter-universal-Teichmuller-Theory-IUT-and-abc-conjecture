import LeanFormal.IUT.Foundations.PAdicAnalytic.TateDeltaIntegral

open scoped ArithmeticFunction.sigma
open ArithmeticFunction PowerSeries
open LeanFormal.IUT
open LeanFormal.IUT.PAdicAnalytic
open LeanFormal.IUT.PAdicAnalytic.General

set_option linter.unusedSectionVars false
noncomputable section

/-!
# Task-120: ellipticity and q-parameter foundation for the general Tate curve

For a complete nonarchimedean field K and q in K with 0 < |q| < 1, this file
proves that the general Tate curve

  TateCurve.weierstrassCurve K q : y^2 + x*y = x^3 + a4(q) x + a6(q)

is an actual elliptic curve: its discriminant is nonzero, hence a unit.

The proof uses the production evaluation identity for the formal discriminant
series DeltaK (TateDeltaIntegral.generalPSEval_DeltaK_eq_delta_no1728) and the
coefficient integrality of DeltaK.  DeltaK has coefficients 0 and 1 in degrees
0 and 1, so

  Delta(q) = q + tail,   ||tail|| <= ||q||^2,

and for q != 0 the ultrametric strict inequality ||q||^2 < ||q|| forces
Delta(q) != 0.  This proves actual ellipticity, not the q-product identity:
the Tate discriminant product Delta(q) = q * prod (1-q^n)^24 and the analytic
point/coordinate uniformization (the named TateUniformizationPointMapGap of the
production Geometry files) remain the exact residual statements.  No source
Pi_v claim, no card.
-/

namespace LeanFormal.IUT.Foundations.TatePointMap

universe u

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
  [CharZero K] [IsUltrametricDist K]

/-- The coefficient of q^0 of the formal discriminant series DeltaK is zero. -/
theorem DeltaK_coeff_zero :
    PowerSeries.coeff 0 (DeltaK (K := K)) = 0 := by
  rw [← DK_eq_DeltaK]
  exact coeff_DK_zero (K := K)

/-- The coefficient of q^1 of the formal discriminant series DeltaK is one. -/
theorem DeltaK_coeff_one :
    PowerSeries.coeff 1 (DeltaK (K := K)) = 1 := by
  rw [← DK_eq_DeltaK]
  exact coeff_DK_one (K := K)

/-- The tail (degrees at least 2) of the evaluation of DeltaK at q has norm at
most ||q||^2. -/
theorem norm_deltaK_tail_le
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) {q : K} (hq : ‖q‖ < 1) :
    ‖∑' x : ↥((({0, 1} : Finset ℕ) : Set ℕ)ᶜ),
        (DeltaK (K := K)).coeff (x : ℕ) * q ^ (x : ℕ)‖ ≤ ‖q‖ ^ 2 := by
  let f : ℕ → K := fun n => (DeltaK (K := K)).coeff n * q ^ n
  have hsum : Summable f :=
    summable_generalPSEval (DeltaK (K := K)) (integral_DeltaK hint) hq
  have hle : ∀ x : ↥((({0, 1} : Finset ℕ) : Set ℕ)ᶜ), ‖f (x : ℕ)‖ ≤ ‖q‖ ^ 2 := by
    intro x
    have hx0 : (x : ℕ) ≠ 0 := by
      intro h
      have hmem : (x : ℕ) ∈ ({0, 1} : Finset ℕ) := by
        rw [h]
        simp
      exact x.2 hmem
    have hx1 : (x : ℕ) ≠ 1 := by
      intro h
      have hmem : (x : ℕ) ∈ ({0, 1} : Finset ℕ) := by
        rw [h]
        simp
      exact x.2 hmem
    have hx2 : 2 ≤ (x : ℕ) := by omega
    have hcoeff : ‖(DeltaK (K := K)).coeff (x : ℕ)‖ ≤ 1 :=
      integral_DeltaK hint (x : ℕ)
    have hf : f (x : ℕ) = (DeltaK (K := K)).coeff (x : ℕ) * q ^ (x : ℕ) := rfl
    calc ‖f (x : ℕ)‖
        = ‖(DeltaK (K := K)).coeff (x : ℕ)‖ * ‖q‖ ^ (x : ℕ) := by
          rw [hf, norm_mul, norm_pow]
      _ ≤ 1 * ‖q‖ ^ (x : ℕ) :=
          mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (norm_nonneg q) _)
      _ = ‖q‖ ^ (x : ℕ) := one_mul _
      _ ≤ ‖q‖ ^ 2 := by
          exact pow_le_pow_of_le_one (norm_nonneg q) hq.le hx2
  haveI : Nonempty ↥((({0, 1} : Finset ℕ) : Set ℕ)ᶜ) := ⟨⟨2, by simp⟩⟩
  exact le_trans (IsUltrametricDist.norm_tsum_le _) (ciSup_le hle)

/-- The evaluation of DeltaK at q differs from q by a tail of norm at most
||q||^2. -/
theorem norm_generalPSEval_DeltaK_sub_q_le
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) {q : K} (hq : ‖q‖ < 1) :
    ‖generalPSEval (DeltaK (K := K)) q - q‖ ≤ ‖q‖ ^ 2 := by
  let f : ℕ → K := fun n => (DeltaK (K := K)).coeff n * q ^ n
  let s : Finset ℕ := {0, 1}
  have hsum : Summable f :=
    summable_generalPSEval (DeltaK (K := K)) (integral_DeltaK hint) hq
  have hsplit := Summable.sum_add_tsum_compl (f := f) (s := s) hsum
  have hfinite : (∑ x ∈ s, f x) = q := by
    simp [s, f, DeltaK_coeff_zero, DeltaK_coeff_one]
  have htotal : (∑' n : ℕ, f n) = q + ∑' x : ↥(((s : Finset ℕ) : Set ℕ)ᶜ), f (x : ℕ) := by
    rw [← hsplit, hfinite]
  have htail : ‖∑' x : ↥(((s : Finset ℕ) : Set ℕ)ᶜ), f (x : ℕ)‖ ≤ ‖q‖ ^ 2 := by
    simpa [s, f] using norm_deltaK_tail_le (K := K) hint hq
  unfold generalPSEval
  rw [htotal]
  simpa using htail

/-- The discriminant of the general Tate curve at q differs from q by a tail of
norm at most ||q||^2. -/
theorem norm_tateCurve_Δ_sub_q_le
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) {q : K} (hq : ‖q‖ < 1) :
    ‖(TateCurve.weierstrassCurve K q).Δ - q‖ ≤ ‖q‖ ^ 2 := by
  rw [← generalPSEval_DeltaK_eq_delta_no1728 (K := K) hint hq]
  exact norm_generalPSEval_DeltaK_sub_q_le (K := K) hint hq

/-- For 0 < |q| < 1 the discriminant of the general Tate curve is nonzero. -/
theorem tateCurve_Δ_ne_zero
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) {q : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    (TateCurve.weierstrassCurve K q).Δ ≠ 0 := by
  have hqpos : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  have hq2lt : ‖q‖ ^ 2 < ‖q‖ := by nlinarith [hqpos, hq]
  have hle := norm_tateCurve_Δ_sub_q_le (K := K) hint hq
  intro hzero
  have hnorm : ‖(TateCurve.weierstrassCurve K q).Δ - q‖ = ‖q‖ := by
    rw [hzero, zero_sub, norm_neg]
  linarith [hle, hq2lt, hnorm.symm ▸ hle]

/-- **Ellipticity of the general Tate curve** for 0 < |q| < 1.  This is the
actual elliptic-curve property, proved from the production DeltaK evaluation
and the leading-term estimate; the q-product formula is not needed for
nonvanishing and remains a separate exact statement. -/
theorem tateWeierstrassCurve_isElliptic
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) {q : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    (TateCurve.weierstrassCurve K q).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  exact isUnit_iff_ne_zero.mpr (tateCurve_Δ_ne_zero (K := K) hint hq0 hq)


/-- In a complete nonarchimedean field every natural-number cast has norm at
most one (the general integer-cast integrality needed by the production
DeltaK evaluation identity). -/
theorem norm_natCast_le_one (n : ℕ) : ‖(n : K)‖ ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h : ((n + 1 : ℕ) : K) = (n : K) + 1 := by push_cast; ring
      rw [h]
      exact le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ih (by simp))

/-- **Unconditional ellipticity of the general Tate curve** for 0 < |q| < 1:
no separate integer-cast hypothesis is needed because nonarchimedean integer
casts are automatically integral. -/
theorem tateWeierstrassCurve_isElliptic_of_norm {q : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    (TateCurve.weierstrassCurve K q).IsElliptic :=
  tateWeierstrassCurve_isElliptic (K := K) norm_natCast_le_one hq0 hq

end LeanFormal.IUT.Foundations.TatePointMap
