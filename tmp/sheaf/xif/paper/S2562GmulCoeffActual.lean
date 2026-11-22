import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2562GmulCoeffActual

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual

lemma G_coeff_eq_zero_of_lt (k : ℕ) (hk : 13 ≤ k) : G.coeff k = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have h : G.natDegree ≤ 12 := by unfold G; compute_degree!
  omega

/-- For n ≥ 12, the coefficient of G*P is the 13-term support sum. -/
lemma G_mul_coeff_ge (P : (ZMod 613)[X]) (n : ℕ) (hn : 12 ≤ n) :
    (G * P).coeff n = ∑ a ∈ Finset.range 13, G.coeff a * P.coeff (n - a) := by
  rw [Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro x hx
    exact Finset.mem_range.mpr (by
      have hx13 : x < 13 := Finset.mem_range.mp hx
      omega)
  · intro x hx hnot
    have hx13 : 13 ≤ x := by
      by_contra h
      exact hnot (Finset.mem_range.mpr (Nat.lt_of_not_ge h))
    rw [G_coeff_eq_zero_of_lt x hx13, zero_mul]

end LeanFormal.IUT.XiFPaper.S2562GmulCoeffActual

end