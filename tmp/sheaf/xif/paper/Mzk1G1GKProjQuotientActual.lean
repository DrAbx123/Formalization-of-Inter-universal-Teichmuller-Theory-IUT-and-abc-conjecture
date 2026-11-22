/- GK §7.3, batch 3a: projective points as a quotient of the compact Fermat sphere
`Y_n(K)` by the norm-one scaling action (route L683). -/
import tmp.sheaf.xif.paper.Mzk1G1GKProjectiveCompactActual
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic

noncomputable section
open scoped Valued WithZeroTopology
open ValuativeRel
namespace LeanFormal.IUT.XiFPaper.Mzk1G1GKProjQuotientActual
open LeanFormal.IUT.XiFPaper.Mzk1G1GKProjectiveCompactActual

variable {K : Type*} [NormedField K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The projective relation on the Fermat sphere: two sphere points are equivalent when
they differ by multiplication by an element of norm one. -/
def projSetoid (n : Nat) : Setoid {v : Fin 3 → K // Ysphere (K := K) (n := n) v} where
  r v w := ∃ c : K, ‖c‖ = 1 ∧ w.1 = fun i => c * v.1 i
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro v
      exact ⟨(1 : K), by simp, by funext i; simp⟩
    · intro v w h
      obtain ⟨c, hc, hw⟩ := h
      refine ⟨c⁻¹, by rw [norm_inv, hc, inv_one], ?_⟩
      rw [hw]
      funext i
      have hne : c ≠ 0 := by
        intro hc0
        rw [hc0, norm_zero] at hc
        norm_num at hc
      rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    · intro v w z h1 h2
      obtain ⟨c, hc, hw⟩ := h1
      obtain ⟨d, hd, hz⟩ := h2
      refine ⟨d * c, by rw [norm_mul, hc, hd, mul_one], ?_⟩
      rw [hz, hw]
      funext i
      rw [mul_assoc]



/-- The set of projective points of the Fermat curve over `K`. -/
abbrev ProjY (n : Nat) : Type _ :=
  Quotient (projSetoid (K := K) n)

/-- Compactness of the projective Fermat curve over a compact local field. -/
theorem projY_compactSpace [T2Space K] (n : Nat) : CompactSpace (ProjY (K := K) n) := by
  haveI : CompactSpace {v : Fin 3 → K // Ysphere (K := K) (n := n) v} :=
    isCompact_iff_compactSpace.mp (isCompact_Ysphere (K := K) (n := n))
  infer_instance

/-- The Fermat sphere is nonempty for positive `n` (the point `(1 : 0 : 1)`). -/
theorem Ysphere_nonempty (n : Nat) (hn : 0 < n) :
    Nonempty {v : Fin 3 → K // Ysphere (K := K) (n := n) v} := by
  let v : Fin 3 → K := fun i => if i = 0 then (1 : K) else if i = 1 then (0 : K) else 1
  have hv0 : v 0 = 1 := by simp [v]
  have hv1 : v 1 = 0 := by simp [v]
  have hv2 : v 2 = 1 := by simp [v]
  have hsphere : Ysphere (K := K) (n := n) v := by
    constructor
    · constructor
      · intro i
        fin_cases i <;> simp [v]
      · exact ⟨0, by rw [hv0]; simp⟩
    · change v 0 ^ n + v 1 ^ n = v 2 ^ n
      rw [hv0, hv1, hv2, one_pow, zero_pow hn.ne']
      norm_num
  exact ⟨⟨v, hsphere⟩⟩

#print axioms projY_compactSpace
#print axioms Ysphere_nonempty
end LeanFormal.IUT.XiFPaper.Mzk1G1GKProjQuotientActual