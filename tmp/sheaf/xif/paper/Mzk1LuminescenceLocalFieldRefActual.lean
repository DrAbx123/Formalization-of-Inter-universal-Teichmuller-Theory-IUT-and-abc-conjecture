import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Adapted local-field lemmas from Luminescence/IUT `local-field/LocalFieldAudit`

Reference adaptation (Mathlib 4.32.2) of the verified declarations in
`tmp/online/Luminescence__IUT/.../local-field/LocalFieldAudit/{Shell,Filtration}.lean`
(originally Mathlib 4.34.0-rc2).  Only the actual p-adic/lattice lemmas are
kept: scalar-layer preservation by a linear equivalence, the unit-ball/norm
dictionary, and the maximal-ideal power/norm/valuation dictionary.

Scope caveat (from the source): no IUT `Ism`, logarithm-image identity,
ramified extension, Kummer choice, or packet is constructed here.

No sorry, axiom, True or placeholder.
-/

set_option autoImplicit false

open scoped Pointwise

namespace LeanFormal.IUT.XiFPaper.Mzk1LuminescenceLocalFieldRefActual

universe u v

section Shell

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- A genuine linear equivalence preserving an arbitrary set preserves every
scalar dilate of that set, including the zero scalar case. -/
theorem image_scalar_layer (e : V ≃ₗ[K] V) (L : Set V)
    (hL : e '' L = L) (a : K) : e '' (a • L) = a • L := by
  calc
    e '' (a • L) = a • e '' L := Set.image_smul_comm e a L (fun x => e.map_smul a x)
    _ = a • L := by rw [hL]

/-- Injectivity upgrades the layer-image equality to membership equivalence. -/
theorem scalar_layer_membership_iff (e : V ≃ₗ[K] V) (L : Set V)
    (hL : e '' L = L) (a : K) (x : V) : e x ∈ a • L ↔ x ∈ a • L := by
  have himage := image_scalar_layer e L hL a
  constructor
  · intro hx
    have him : e x ∈ e '' (a • L) := by rwa [himage]
    obtain ⟨y, hy, hey⟩ := him
    exact e.injective hey ▸ hy
  · intro hx
    rw [← himage]
    exact ⟨x, hx, rfl⟩

/-- Explicit measurement/layer correspondence converts linear layer preservation
into preservation of all displayed strict thresholds. -/
theorem threshold_iff_of_layers (e : V ≃ₗ[K] V) (L : Set V)
    (hL : e '' L = L) (a : Int → K) (cutoff : Int → Int) (measure : V → Int)
    (hmeasure : ∀ (n : Int) (y : V), y ≠ 0 →
      (y ∈ a n • L ↔ cutoff n < measure y))
    (x : V) (hx : x ≠ 0) (n : Int) :
    cutoff n < measure (e x) ↔ cutoff n < measure x := by
  have hex : e x ≠ 0 := by
    intro hzero
    apply hx
    apply e.injective
    simpa using hzero
  exact (hmeasure n (e x) hex).symm.trans
    ((scalar_layer_membership_iff e L hL (a n) x).trans (hmeasure n x hx))

/-- The actual Mathlib `Q_p`-module instance with scalar layers `p^n L`. -/
theorem padic_threshold_iff (p : Nat) [Fact p.Prime]
    {W : Type v} [AddCommGroup W] [Module ℚ_[p] W]
    (e : W ≃ₗ[ℚ_[p]] W) (L : Set W) (hL : e '' L = L)
    (cutoff : Int → Int) (measure : W → Int)
    (hmeasure : ∀ (n : Int) (y : W), y ≠ 0 →
      (y ∈ ((p : ℚ_[p]) ^ n) • L ↔ cutoff n < measure y))
    (x : W) (hx : x ≠ 0) (n : Int) :
    cutoff n < measure (e x) ↔ cutoff n < measure x := by
  exact threshold_iff_of_layers e L hL (fun m => (p : ℚ_[p]) ^ m)
    cutoff measure hmeasure x hx n

/-- For the actual Mathlib p-adic norm unit ball, preserving the ball implies
preserving all of its `p^n`-layers. -/
theorem padic_unitBall_layer_membership_iff (p : Nat) [Fact p.Prime]
    (e : ℚ_[p] ≃ₗ[ℚ_[p]] ℚ_[p])
    (hball : e '' {y : ℚ_[p] | ‖y‖ ≤ 1} = {y : ℚ_[p] | ‖y‖ ≤ 1})
    (n : Int) (x : ℚ_[p]) :
    e x ∈ ((p : ℚ_[p]) ^ n) • {y : ℚ_[p] | ‖y‖ ≤ 1} ↔
      x ∈ ((p : ℚ_[p]) ^ n) • {y : ℚ_[p] | ‖y‖ ≤ 1} := by
  exact scalar_layer_membership_iff e {y : ℚ_[p] | ‖y‖ ≤ 1} hball
    ((p : ℚ_[p]) ^ n) x

end Shell

section Filtration

variable (p : Nat) [hp : Fact p.Prime]

/-- The actual p-adic norm unit ball, including zero. -/
def ball : Set ℚ_[p] := {x | ‖x‖ ≤ 1}

/-- The image in `Q_p` of the n-th power of the actual maximal ideal of `Z_p`. -/
def integerIdealImage (n : Nat) : Set ℚ_[p] :=
  ((↑) : ℤ_[p] → ℚ_[p]) ''
    (↑((IsLocalRing.maximalIdeal ℤ_[p]) ^ n) : Set ℤ_[p])

/-- A nonzero scalar dilate of the unit ball is exactly its norm ball. -/
theorem mem_smul_ball_iff_norm_le (a x : ℚ_[p]) (ha : a ≠ 0) :
    x ∈ a • ball p ↔ ‖x‖ ≤ ‖a‖ := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    change ‖a * y‖ ≤ ‖a‖
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hy (norm_nonneg a)).trans_eq (mul_one _)
  · intro hx
    refine ⟨x / a, ?_, ?_⟩
    · change ‖x / a‖ ≤ 1
      rw [norm_div, div_le_one₀ (norm_pos_iff.mpr ha)]
      exact hx
    · change a * (x / a) = x
      exact mul_div_cancel₀ x ha

/-- All integer scalar layers have a proved actual norm interpretation. -/
theorem mem_zpow_ball_iff_norm_le (n : Int) (x : ℚ_[p]) :
    x ∈ ((p : ℚ_[p]) ^ n) • ball p ↔ ‖x‖ ≤ (p : ℝ) ^ (-n) := by
  rw [mem_smul_ball_iff_norm_le p _ _ (zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)),
    Padic.norm_p_zpow]

/-- The valuation interpretation of those layers explicitly excludes zero. -/
theorem mem_zpow_ball_iff_le_valuation (n : Int) (x : ℚ_[p]) (hx : x ≠ 0) :
    x ∈ ((p : ℚ_[p]) ^ n) • ball p ↔ n ≤ x.valuation := by
  rw [mem_zpow_ball_iff_norm_le, Padic.norm_eq_zpow_neg_valuation hx,
    zpow_le_zpow_iff_right₀, neg_le_neg_iff]
  exact_mod_cast hp.out.one_lt

/-- Actual powers of the maximal ideal are norm layers, with zero included. -/
theorem mem_maximalIdeal_pow_iff_norm_le (n : Nat) (x : ℤ_[p]) :
    x ∈ (IsLocalRing.maximalIdeal ℤ_[p]) ^ n ↔
      ‖x‖ ≤ (p : ℝ) ^ (-(n : Int)) := by
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow]
  exact (PadicInt.norm_le_pow_iff_mem_span_pow x n).symm

/-- The actual ideal/valuation correspondence, with its nonzero premise. -/
theorem mem_maximalIdeal_pow_iff_le_valuation (n : Nat) (x : ℤ_[p]) (hx : x ≠ 0) :
    x ∈ (IsLocalRing.maximalIdeal ℤ_[p]) ^ n ↔ n ≤ x.valuation := by
  rw [mem_maximalIdeal_pow_iff_norm_le]
  exact PadicInt.norm_le_pow_iff_le_valuation x hx n

end Filtration

end LeanFormal.IUT.XiFPaper.Mzk1LuminescenceLocalFieldRefActual
