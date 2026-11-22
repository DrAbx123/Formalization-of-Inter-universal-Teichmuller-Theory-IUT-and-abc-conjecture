import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
noncomputable section
namespace TestCyclic
theorem gcd_dvd_of_dvd_div {N a b : ℕ} (hN : 0 < N)
    (h : N / Nat.gcd a N ∣ N / Nat.gcd b N) :
    Nat.gcd b N ∣ a := by
  let A := Nat.gcd a N
  let B := Nat.gcd b N
  have hA : A ∣ N := Nat.gcd_dvd_right a N
  have hB : B ∣ N := Nat.gcd_dvd_right b N
  have hAB : Nat.gcd A B ∣ N := (Nat.gcd_dvd_left A B).trans hA
  have hgcdpos : 0 < Nat.gcd A B := Nat.gcd_pos_of_pos_right A (Nat.pos_of_dvd_of_pos hB hN)
  have hBpos : 0 < B := Nat.pos_of_dvd_of_pos hB hN
  have hlcm : Nat.lcm (N / A) (N / B) = N / B :=
    (Nat.lcm_eq_right_iff_dvd).mpr h
  rw [Nat.div_lcm_eq_div_gcd hA hB] at hlcm
  have h1 : N = (N / B) * Nat.gcd A B :=
    (Nat.div_eq_iff_eq_mul_left hgcdpos hAB).mp hlcm
  have h2 : N = (N / B) * B := (Nat.div_mul_cancel hB).symm
  have hNBpos : 0 < N / B := Nat.div_pos (Nat.le_of_dvd hN hB) hBpos
  have hgB : Nat.gcd A B = B := Nat.mul_left_cancel hNBpos (h1.symm.trans h2)
  have hBA : B ∣ A := Nat.gcd_eq_right_iff_dvd.mp hgB
  exact hBA.trans (Nat.gcd_dvd_left a N)


theorem zpowers_le_of_orderOf_dvd {G : Type*} [Group G] [Finite G] {x : G} {a b : ℕ}
    (h : orderOf (x ^ a) ∣ orderOf (x ^ b)) :
    Subgroup.zpowers (x ^ a) ≤ Subgroup.zpowers (x ^ b) := by
  by_cases ha : a = 0
  · subst a
    simp
  by_cases hb : b = 0
  · subst b
    have h1 : orderOf (x ^ a) = 1 := Nat.dvd_one.mp (by simpa using h)
    have hx : x ^ a = 1 := orderOf_eq_one_iff.mp h1
    rw [hx]
    simp
  let N := orderOf x
  let d := Nat.gcd b N
  have hN : 0 < N := orderOf_pos x
  have hdvd : d ∣ a := by
    apply gcd_dvd_of_dvd_div hN
    simpa [N, d, orderOf_pow' x ha, orderOf_pow' x hb, Nat.gcd_comm] using h
  let q := a / d
  have haq : a = d * q := by
    rw [mul_comm]
    exact (Nat.div_mul_cancel hdvd).symm
  refine Subgroup.zpowers_le.mpr ?_
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨Nat.gcdA b N * (q : ℤ), ?_⟩
  rw [← zpow_natCast x b, ← zpow_mul]
  rw [← zpow_natCast x a]
  rw [zpow_eq_zpow_iff_modEq]
  have hbez := congrArg (fun z : ℤ => z * (q : ℤ)) (Nat.gcd_eq_gcd_ab b N)
  have hqcast : (d : ℤ) * (q : ℤ) = (a : ℤ) := by
    exact_mod_cast haq.symm
  have hdecomp : (b : ℤ) * (Nat.gcdA b N * (q : ℤ)) =
      (a : ℤ) - (N : ℤ) * (Nat.gcdB b N * (q : ℤ)) := by
    nlinarith [hbez, hqcast]
  rw [Int.modEq_iff_dvd, hdecomp]
  ring_nf
  rw [mul_assoc]
  change (N : ℤ) ∣ (N : ℤ) * (Nat.gcdB b N * (q : ℤ))
  exact dvd_mul_right (N : ℤ) (Nat.gcdB b N * (q : ℤ))


theorem cyclic_subgroup_le_iff_card_dvd {G : Type*} [Group G] [Finite G] [IsCyclic G]
    (H K : Subgroup G) : H ≤ K ↔ Nat.card H ∣ Nat.card K := by
  constructor
  · exact Subgroup.card_dvd_of_le
  · intro hdvd
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
    obtain ⟨a, hHa⟩ := (Subgroup.le_zpowers_iff g H).mp fun x _ => hg x
    obtain ⟨b, hKb⟩ := (Subgroup.le_zpowers_iff g K).mp fun x _ => hg x
    rw [hHa, hKb] at hdvd ⊢
    rw [Nat.card_zpowers, Nat.card_zpowers] at hdvd
    exact zpowers_le_of_orderOf_dvd hdvd

end TestCyclic
end
