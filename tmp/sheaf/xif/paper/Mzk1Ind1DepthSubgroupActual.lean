import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Ind1DepthSubgroupActual

universe uA
variable {A : Type uA} [CommGroup A]

/-- The `r`-depth subgroup `D_r(A) = ⋂_n r^n A`. -/
def depthSubgroup (r : Nat) (A : Type uA) [CommGroup A] : Subgroup A :=
  ⨅ n : Nat, (powMonoidHom (α := A) (r ^ n)).range

theorem mem_depthSubgroup (r : Nat) (x : A) :
    x ∈ depthSubgroup r A ↔ ∀ n : Nat, ∃ y : A, y ^ (r ^ n) = x := by
  simp [depthSubgroup, Subgroup.mem_iInf, MonoidHom.mem_range]

lemma nat_lt_pow_self {r : Nat} (hr : 1 < r) : ∀ n : Nat, n < r ^ n
  | 0 => by simp
  | n + 1 => by
    have ih : n < r ^ n := nat_lt_pow_self hr n
    have hle : n + 1 ≤ r ^ n := Nat.succ_le_of_lt ih
    have hpos : 0 < r := by omega
    have hpow_pos : 0 < r ^ n := pow_pos hpos n
    have hmul : r ^ n < r ^ n * r := by
      calc
        r ^ n = r ^ n * 1 := (mul_one _).symm
        _ < r ^ n * r := mul_lt_mul_of_pos_left hr hpow_pos
    calc
      n + 1 ≤ r ^ n := hle
      _ < r ^ n * r := hmul
      _ = r ^ (n + 1) := by rw [pow_succ]

lemma int_eq_zero_of_forall_dvd_pow {r : Nat} (hr : 1 < r) {k : ℤ}
    (h : ∀ n : Nat, ((r ^ n : Nat) : ℤ) ∣ k) : k = 0 := by
  by_contra hk
  let n := k.natAbs + 1
  have hdvd : ((r ^ n : Nat) : ℤ) ∣ k := h n
  have hle : r ^ n ≤ k.natAbs :=
    by simpa [Int.natAbs_natCast] using Int.natAbs_le_of_dvd_ne_zero hdvd hk
  have hlt : k.natAbs < r ^ n :=
    by have := nat_lt_pow_self hr n; omega
  omega

def DepthSubgroupEqualsKernel (v : A →* Multiplicative ℤ) (r : Nat) : Prop :=
  depthSubgroup r A = v.ker

/-- §5.1 abstract depth theorem: if the kernel of a `ℤ`-valued valuation map
is infinitely `r`-divisible, then `D_r(A) = ker v`. -/
theorem DepthSubgroupEqualsKernel_of_divisible
    (v : A →* Multiplicative ℤ) {r : Nat} (hr : 1 < r)
    (hdiv : ∀ x : A, v x = 1 → ∀ n : Nat, ∃ y : A, y ^ (r ^ n) = x) :
    DepthSubgroupEqualsKernel v r := by
  change depthSubgroup r A = v.ker
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_ker]
    have hk : Multiplicative.toAdd (v x) = 0 := by
      apply int_eq_zero_of_forall_dvd_pow hr
      intro n
      have hxmem : x ∈ (powMonoidHom (α := A) (r ^ n)).range := by
        rw [depthSubgroup] at hx
        exact Subgroup.mem_iInf.mp hx n
      rcases MonoidHom.mem_range.mp hxmem with ⟨y, hy⟩
      refine ⟨Multiplicative.toAdd (v y), ?_⟩
      have hvxy : v x = (v y) ^ (r ^ n) := by
        calc
          v x = v ((powMonoidHom (r ^ n)) y) := by rw [hy]
          _ = v (y ^ (r ^ n)) := by
            rw [show (powMonoidHom (r ^ n)) y = y ^ (r ^ n) from rfl]
          _ = (v y) ^ (r ^ n) := map_pow (v) y (r ^ n)
      rw [hvxy]
      simp [nsmul_eq_mul]
    apply Multiplicative.toAdd.injective
    simpa using hk
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    rw [depthSubgroup]
    rw [Subgroup.mem_iInf]
    intro n
    rcases hdiv x hx n with ⟨y, hy⟩
    exact MonoidHom.mem_range.mpr ⟨y, hy⟩

#print axioms DepthSubgroupEqualsKernel_of_divisible
#print axioms mem_depthSubgroup
#print axioms int_eq_zero_of_forall_dvd_pow
end LeanFormal.IUT.XiFPaper.Mzk1Ind1DepthSubgroupActual