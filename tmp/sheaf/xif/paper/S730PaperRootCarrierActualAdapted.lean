import LeanFormal.IUT.Foundations.LocalFields.LocalRootNormRepresentative

/-!
# S730: paper root carrier research — divisibility obstruction and mu_{2l}-torsor

This file records two paper-faithful facts about the q[2u] carrier.

## 1. Valuation obstruction (no-go for the completion/root-stack shortcut)

If a nonzero integral element q of a mixed-characteristic local field has an
n-th root r in the same local field, then n divides the DVR order of q.
This is the exact valuation-theoretic obstruction: a root stack/mu_n-gerbe over
the completion cannot manufacture a root whose valuation is not integral.
Applied to n = 2*l, the paper's assertion that q[1u] admits a 2l-th root in
O^triangle_{K_v} forces 2*l | ord(q[1u]).  The repository's qVFamily has
Nat.Coprime (order) l, so it cannot be the paper q[1u].

## 2. mu_{2l}-torsor and root-choice invariance

For any unit q of a normed field, the 2l-th roots of q form a mu_{2l}-torsor.
All roots differ by an element of mu_{2l}; mu_{2l} has norm one; hence the norm
of every theta value root^(j^2) is independent of the chosen root.  This is the
precise paper-faithful content of the root stack: it records the mu_{2l}
indeterminacy, and the log-volume/hull radius sees only the common norm, not the
choice of root.

No root is fabricated, no completion root is asserted, and no inequality is
claimed.
-/

noncomputable section
set_option linter.overlappingInstances false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S730PaperRootCarrierActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.LocalRootNormRepresentative
open LeanFormal.IUT.LocalFieldIntegralUnits

/-! ## 1. A root in the local field forces divisibility of the order -/

/-- If q has an n-th root r in a mixed-characteristic local field, then n
divides the DVR order of q.  This is the exact obstruction to a
completion-valued 2l-th root of an element whose order is prime to l. -/
theorem root_forces_dvd (p : Nat) [Fact p.Prime] {K : Type*}
    [NormedField K] [CharZero K] [CompleteSpace K]
    [IsUltrametricDist K] [ProperSpace K] [NormedAlgebra ℚ_[p] K]
    [IsDiscreteValuationRing (Integers K)]
    (q r : Integers K) (n : Nat) (hn : 0 < n)
    (hr : (r : K) ^ n = (q : K)) (hq : q ≠ 0) :
    n ∣ (IsDiscreteValuationRing.addVal (Integers K) q).toNat := by
  have hr0 : r ≠ 0 := by
    intro h
    apply hq
    have hzero : (q : K) = 0 := by
      rw [← hr, h]
      exact zero_pow hn.ne'
    exact Subtype.ext hzero
  refine (@exists_integral_norm_root_iff_order_dvd p _ K _ _ _ _ _ _ _ q hq n).mp ?_
  refine ⟨r, hr0, ?_⟩
  rw [← norm_pow, hr]

/-- Paper form: a 2l-th root of an integral q forces 2l | ord(q). -/
theorem paper_twoLRoot_forces_dvd (p : Nat) [Fact p.Prime] {K : Type*}
    [NormedField K] [CharZero K] [CompleteSpace K]
    [IsUltrametricDist K] [ProperSpace K] [NormedAlgebra ℚ_[p] K]
    [IsDiscreteValuationRing (Integers K)]
    {l : PrimeGeFive} (q r : Integers K)
    (hr : (r : K) ^ (2 * l.value) = (q : K)) (hq : q ≠ 0) :
    (2 * l.value) ∣
      (IsDiscreteValuationRing.addVal (Integers K) q).toNat :=
  root_forces_dvd p q r (2 * l.value)
    (Nat.mul_pos (by norm_num) l.prime.pos) hr hq

/-! ## 2. The mu_{2l}-torsor of roots and root-choice invariance -/

variable {K : Type*} [NormedField K]
variable {n : Nat} (hn : 0 < n)
variable (q : Kˣ)

/-- The mu_n-torsor of n-th roots of a unit q. -/
structure RootTorsor (n : Nat) (q : Kˣ) where
  root : Kˣ
  root_pow : root ^ n = q

/-- The group mu_n of n-th roots of unity. -/
def muN (n : Nat) (q : Kˣ) : Subgroup (Kˣ) where
  carrier := {ζ | ζ ^ n = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change (a * b) ^ n = 1
    rw [mul_pow, ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    change (a⁻¹) ^ n = 1
    rw [inv_pow, ha, inv_one]

/-- The mu_n action on the root torsor. -/
def muAction {n : Nat} {q : Kˣ} (ζ : muN n q) (r : RootTorsor n q) :
    RootTorsor n q where
  root := ζ.1 * r.root
  root_pow := by
    rw [mul_pow, ζ.2, r.root_pow, one_mul]

/-- The ratio of any two roots lies in mu_n.  This is the paper's mu_{2l}
indeterminacy of q[2u]. -/
theorem root_ratio_mem_mu {n : Nat} {q : Kˣ} (r s : RootTorsor n q) :
    s.root / r.root ∈ muN n q := by
  change (s.root / r.root) ^ n = 1
  rw [div_pow, s.root_pow, r.root_pow]
  rw [div_eq_mul_inv, mul_inv_cancel]

/-- The mu_n action is transitive: every two roots differ by an element of mu_n. -/
theorem exists_mu_mul_eq {n : Nat} {q : Kˣ} (r s : RootTorsor n q) :
    ∃ ζ : muN n q, ζ.1 * r.root = s.root := by
  refine ⟨⟨s.root / r.root, root_ratio_mem_mu r s⟩, ?_⟩
  exact div_mul_cancel s.root r.root

/-- A mu_n element has norm one. -/
theorem mu_norm_eq_one {n : Nat} {q : Kˣ} (hn : 0 < n) (ζ : muN n q) :
    ‖((ζ.1 : Kˣ) : K)‖ = 1 := by
  have hpow_val : ((ζ.1 : Kˣ) : K) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, ζ.2, Units.val_one]
  have hpow : ‖((ζ.1 : Kˣ) : K)‖ ^ n = 1 := by
    rw [← norm_pow, hpow_val, norm_one]
  have hpos : 0 ≤ ‖((ζ.1 : Kˣ) : K)‖ := norm_nonneg _
  rcases lt_trichotomy ‖((ζ.1 : Kˣ) : K)‖ 1 with h | h | h
  · have hlt : ‖((ζ.1 : Kˣ) : K)‖ ^ n < 1 := pow_lt_one₀ hpos h hn.ne'
    linarith
  · exact h
  · have hgt : 1 < ‖((ζ.1 : Kˣ) : K)‖ ^ n := one_lt_pow₀ h hn.ne'
    linarith

/-- The norm of a root is independent of the chosen n-th root. -/
theorem root_norm_independent {n : Nat} {q : Kˣ} (hn : 0 < n)
    (r s : RootTorsor n q) :
    ‖(r.root : K)‖ = ‖(s.root : K)‖ := by
  obtain ⟨ζ, hζ⟩ := exists_mu_mul_eq r s
  rw [← hζ, Units.val_mul, norm_mul, mu_norm_eq_one hn ζ, one_mul]

/-- The norm of the m-th power of a root is independent of the root choice.
For the theta values root^(j^2), this is the precise mu_{2l}-invariance of the
hull radii. -/
theorem root_pow_norm_independent {n : Nat} {q : Kˣ} (hn : 0 < n)
    (r s : RootTorsor n q) (m : Nat) :
    ‖(r.root : K) ^ m‖ = ‖(s.root : K) ^ m‖ := by
  simp only [norm_pow]
  rw [root_norm_independent hn r s]

#print axioms root_forces_dvd
#print axioms paper_twoLRoot_forces_dvd
#print axioms root_ratio_mem_mu
#print axioms root_norm_independent

end LeanFormal.IUT.XiFPaper.S730PaperRootCarrierActualAdapted

end
