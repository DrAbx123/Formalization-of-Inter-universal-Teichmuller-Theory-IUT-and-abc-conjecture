import LeanFormal.IUT.IUTII.Kummer.AbsoluteKummerInjection
import LeanFormal.IUT.IUTII.Kummer.AbsoluteKummerQuotient

/-!
# Mzk1AbsoluteKummerKernelLawActual — derived kernel/quotient laws for the absolute Kummer
class (new theorems from the existing injection/quotient assets). No copies/bookkeeping.
No axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1AbsoluteKummerKernelLawActual

open LeanFormal.IUT
open LeanFormal.IUT.AbsoluteKummerQuotient

/-- Derived: n-th powers lie in the n-th-power subgroup. -/
theorem pow_mem_nthPowerSubgroup {K : Type*} [Field K] [CharZero K] {n : ℕ} [NeZero n]
    (a : Kˣ) : a ^ n ∈ nthPowerSubgroup (K := K) (n := n) := by
  rw [mem_nthPowerSubgroup]
  exact ⟨a, rfl⟩

/-- Derived: the identity lies in the n-th-power subgroup. -/
theorem one_mem_nthPowerSubgroup {K : Type*} [Field K] [CharZero K] {n : ℕ} [NeZero n] :
    (1 : Kˣ) ∈ nthPowerSubgroup (K := K) (n := n) := by
  rw [mem_nthPowerSubgroup]
  exact ⟨1, one_pow n⟩

/-- Derived: inverses of n-th powers are n-th powers. -/
theorem inv_mem_nthPowerSubgroup {K : Type*} [Field K] [CharZero K] {n : ℕ} [NeZero n]
    {a : Kˣ} (ha : a ∈ nthPowerSubgroup (K := K) (n := n)) :
    a⁻¹ ∈ nthPowerSubgroup (K := K) (n := n) := by
  rw [mem_nthPowerSubgroup] at ha ⊢
  rcases ha with ⟨b, hb⟩
  exact ⟨b⁻¹, by rw [inv_pow, hb]⟩

/-- Derived: the n-th-power subgroup is normal. -/
theorem nthPowerSubgroup_normal {K : Type*} [Field K] [CharZero K] {n : ℕ} [NeZero n] :
    (nthPowerSubgroup (K := K) (n := n)).Normal :=
  inferInstance

/-- Derived: kernel characterization of the absolute Kummer class. -/
theorem absoluteKummerMap_eq_one_iff_mem {K : Type*} [Field K] [CharZero K] {n : ℕ}
    [NeZero n] (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n)) (a : Kˣ) :
    AbsoluteKummerInjection.absoluteKummerMap hμ a = 1 ↔
      a ∈ nthPowerSubgroup (K := K) (n := n) := by
  rw [mem_nthPowerSubgroup]
  exact AbsoluteKummerInjection.absoluteKummerMap_eq_one_iff hμ a

/-- Derived: two units have the same Kummer class iff their quotient is an n-th power. -/
theorem kummerClass_eq_iff_inv_mul {K : Type*} [Field K] [CharZero K] {n : ℕ} [NeZero n]
    (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n)) (a b : Kˣ) :
    AbsoluteKummerInjection.absoluteKummerMap hμ a =
        AbsoluteKummerInjection.absoluteKummerMap hμ b ↔
      a⁻¹ * b ∈ nthPowerSubgroup (K := K) (n := n) := by
  rw [← absoluteKummerMapQuotient_mk (K := K) (n := n) hμ a,
    ← absoluteKummerMapQuotient_mk (K := K) (n := n) hμ b,
    (absoluteKummerMapQuotient_injective (K := K) (n := n) hμ).eq_iff,
    QuotientGroup.eq]

#check pow_mem_nthPowerSubgroup
#check one_mem_nthPowerSubgroup
#check inv_mem_nthPowerSubgroup
#check nthPowerSubgroup_normal
#check absoluteKummerMap_eq_one_iff_mem
#check kummerClass_eq_iff_inv_mul

end LeanFormal.IUT.XiFPaper.Mzk1AbsoluteKummerKernelLawActual
end
