import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.G1KvCompactActual
open LeanFormal.IUT
open Set

/-- The local boundedness/non-degeneracy condition at a single real-valued
place.  For a place v and an element lam write a = v lam and b = v (lam - 1).
The three conjuncts express, respectively: the chordal distance from 0 is at
least delta (delta <= min a 1), the chordal distance from infinity is at least
delta (delta * max 1 a <= 1), and the chordal distance from 1 is at least delta
(delta * max 1 a <= b).  No inverses occur, so the conditions are robust under
the integrality/compactness arguments below. -/
def LocalCondition (δ a b : ℝ) : Prop :=
  δ ≤ min a 1 ∧ δ * max 1 a ≤ 1 ∧ δ * max 1 a ≤ b

/-- Actual data of a compact local domain K_V avoiding {0,1,infinity}:
V is the finite set of rational primes at which the non-archimedean local
conditions are imposed, and delta is the positive radius of the domain. -/
structure KvData where
  /-- The finite set of rational primes whose extensions are constrained. -/
  V : Finset ℕ
  /-- The positive radius of the local domain. -/
  δ : ℝ
  δ_pos : 0 < δ
  δ_lt_one : δ < 1

variable {K : Type*} [Field K] [NumberField K]

/-- The finite place v of K lies over the rational prime p. -/
def PlaceOver (v : NumberField.FinitePlace K) (p : ℕ) : Prop :=
  v (((p : ℚ) : K)) ≠ 1

/-- The actual local domain K_V: at every archimedean place of K, and at every
finite place lying over a prime in V, the local value of lam is bounded and
bounded away from 0, 1 and infinity.  This is the Lean form of the product of
the compact sets {z : dist(z, {0,1,infinity}) >= delta} of the route
(section 7.3, (E2)). -/
def InKv (D : KvData) (lam : K) : Prop :=
  (∀ v : NumberField.InfinitePlace K, LocalCondition D.δ (v lam) (v (lam - 1))) ∧
  (∀ v : NumberField.FinitePlace K, (∃ p ∈ D.V, PlaceOver v p) →
      LocalCondition D.δ (v lam) (v (lam - 1)))

/-- The set of possible local absolute values at one place of the domain. -/
def LocalValueSet (δ : ℝ) : Set ℝ :=
  {a : ℝ | δ ≤ min a 1 ∧ δ * max 1 a ≤ 1}

/-- The possible local values form the interval [delta, delta^-1]. -/
theorem localValueSet_eq_Icc {δ : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 1) :
    LocalValueSet δ = Icc δ δ⁻¹ := by
  ext a
  constructor
  · rintro ⟨h2, h3⟩
    have hδa : δ ≤ a := le_trans h2 (min_le_left _ _)
    have ha_pos : 0 < a := lt_of_lt_of_le h0 hδa
    refine ⟨hδa, ?_⟩
    by_cases ha1 : a ≤ 1
    · have h1inv : (1 : ℝ) ≤ δ⁻¹ := (one_le_inv₀ h0).mpr h1
      linarith
    · push_neg at ha1
      have hmax : max 1 a = a := max_eq_right ha1.le
      rw [hmax] at h3
      have h3' : a * δ ≤ 1 := by rw [mul_comm]; exact h3
      rw [inv_eq_one_div, le_div_iff₀ h0]
      exact h3'
  · rintro ⟨hδa, haδinv⟩
    have ha_pos : 0 < a := lt_of_lt_of_le h0 hδa
    refine ⟨le_min hδa h1, ?_⟩
    by_cases ha1 : a ≤ 1
    · have hmax : max 1 a = 1 := max_eq_left ha1
      rw [hmax, mul_one]
      linarith
    · push_neg at ha1
      have hmax : max 1 a = a := max_eq_right ha1.le
      rw [hmax]
      have h3 : δ * a ≤ δ * δ⁻¹ := mul_le_mul_of_nonneg_left haδinv h0.le
      rwa [mul_inv_cancel₀ h0.ne'] at h3

/-- The local domain of possible values is compact: it is the interval
[delta, delta^-1].  This is the honest compactness content of K_V. -/
theorem localValueSet_isCompact {δ : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 1) :
    IsCompact (LocalValueSet δ) := by
  rw [localValueSet_eq_Icc h0 h1]
  exact isCompact_Icc

/-- At an archimedean place the local value lies in the compact set of possible
values. -/
theorem InKv.arch_mem (D : KvData) {lam : K} (h : InKv D lam)
    (v : NumberField.InfinitePlace K) : v lam ∈ LocalValueSet D.δ :=
  ⟨(h.1 v).1, (h.1 v).2.1⟩

/-- Archimedean boundedness: |lam|_v <= delta^-1 at every infinite place. -/
theorem InKv.arch_bound (D : KvData) {lam : K} (h : InKv D lam)
    (v : NumberField.InfinitePlace K) : v lam ≤ D.δ⁻¹ := by
  have h3 : D.δ * max 1 (v lam) ≤ 1 := (h.1 v).2.1
  by_cases ha1 : v lam ≤ 1
  · have h1inv : (1 : ℝ) ≤ D.δ⁻¹ := (one_le_inv₀ D.δ_pos).mpr (le_of_lt D.δ_lt_one)
    linarith
  · push_neg at ha1
    have hmax : max 1 (v lam) = v lam := max_eq_right ha1.le
    rw [hmax] at h3
    have h3' : v lam * D.δ ≤ 1 := by rw [mul_comm]; exact h3
    rw [inv_eq_one_div, le_div_iff₀ D.δ_pos]
    exact h3'

/-- At every archimedean place the local value of lam is nonzero, i.e. lam
does not reduce to the point 0 at v. -/
theorem InKv.arch_apply_ne_zero (D : KvData) {lam : K} (h : InKv D lam)
    (v : NumberField.InfinitePlace K) : v lam ≠ 0 := by
  have hδa : D.δ ≤ v lam := le_trans (h.1 v).1 (min_le_left _ _)
  intro hzero
  rw [hzero] at hδa
  exact (not_le.mpr D.δ_pos) hδa

/-- No archimedean place sends lam - 1 to 0, i.e. lam does not reduce to the
point 1. -/
theorem InKv.arch_sub_one_ne_zero (D : KvData) {lam : K} (h : InKv D lam)
    (v : NumberField.InfinitePlace K) : v (lam - 1) ≠ 0 := by
  have h3 := (h.1 v).2.2
  have hmax : 0 < max 1 (v lam) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hpos : 0 < D.δ * max 1 (v lam) := mul_pos D.δ_pos hmax
  intro hzero
  rw [hzero] at h3
  exact (not_le.mpr hpos) h3

/-- Actual non-vanishing: an element of the local domain is not 0. -/
theorem InKv.ne_zero (D : KvData) {lam : K} (h : InKv D lam) : lam ≠ 0 := by
  intro hzero
  let v : NumberField.InfinitePlace K :=
    Classical.choice (inferInstance : Nonempty (NumberField.InfinitePlace K))
  exact InKv.arch_apply_ne_zero D h v (by rw [hzero, map_zero])

/-- Actual non-vanishing of lam - 1: an element of the local domain is not 1. -/
theorem InKv.ne_one (D : KvData) {lam : K} (h : InKv D lam) : lam ≠ 1 := by
  intro hlam
  let v : NumberField.InfinitePlace K :=
    Classical.choice (inferInstance : Nonempty (NumberField.InfinitePlace K))
  exact InKv.arch_sub_one_ne_zero D h v (by rw [hlam, sub_self, map_zero])

/-- Nonemptiness of the actual local domain when V is empty: the archimedean
conditions are satisfied by lam = 2 over Q for every delta < 1/2.  This shows
that K_V is not an empty set. -/
theorem kv_nonempty_emptyV {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1 / 2) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (lam : K),
      InKv ⟨∅, δ, h0, lt_trans h1 (by norm_num)⟩ lam := by
  refine ⟨ℚ, inferInstance, inferInstance, (2 : ℚ), ?_⟩
  constructor
  · intro v
    rw [Rat.infinitePlace_apply, Rat.infinitePlace_apply]
    have h2q : |(2 : ℚ)| = 2 := by norm_num
    have h1q : |((2 : ℚ) - 1)| = 1 := by norm_num
    rw [h2q, h1q]
    have hcast2 : (((2 : ℚ)) : ℝ) = 2 := by norm_num
    have hcast1 : (((1 : ℚ)) : ℝ) = 1 := by norm_num
    rw [hcast2, hcast1]
    unfold LocalCondition
    have hmax : max (1 : ℝ) 2 = 2 := max_eq_right (by norm_num)
    refine ⟨le_min (by linarith) (by linarith), ?_, ?_⟩
    · rw [hmax]
      linarith
    · rw [hmax]
      linarith
  · intro v hv
    obtain ⟨p, hp, _⟩ := hv
    exact absurd hp (by simp)

#print axioms localValueSet_isCompact
#print axioms kv_nonempty_emptyV

end LeanFormal.IUT.XiFPaper.G1KvCompactActual
end