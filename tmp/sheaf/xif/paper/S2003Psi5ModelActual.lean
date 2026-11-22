import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual
import tmp.sheaf.xif.paper.S1942PrePsiFiveActual
import tmp.sheaf.xif.paper.S2132D5FactorizationActual
import tmp.sheaf.xif.paper.S2289QE5DegreeActual
import Mathlib.Algebra.Polynomial.Roots

noncomputable section
open Polynomial
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S1942PrePsiFiveActual
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S2289QE5DegreeActual

namespace LeanFormal.IUT.XiFPaper.S2003Psi5ModelActual

set_option maxHeartbeats 20000000 in
theorem S2003Psi5Z_model :
    S2132Psi5Z.map (Int.castRingHom ℚ) =
      C ((2 : ℚ) ^ 36) * S2057Psi5Q := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq' _ _
    ((Finset.range 13).image (fun n : ℕ => (n : ℚ)))
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    have hn13 : n < 13 := Finset.mem_range.mp hn
    interval_cases n <;>
      norm_num [S2057Psi5Q, S2132Psi5Z, S1942_preΨ_five,
        WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
        S1667Curve, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  · have hL : (S2132Psi5Z.map (Int.castRingHom ℚ)).natDegree ≤ 12 := by
      calc (S2132Psi5Z.map (Int.castRingHom ℚ)).natDegree ≤ S2132Psi5Z.natDegree := Polynomial.natDegree_map_le
        _ = 12 := by unfold S2132Psi5Z; compute_degree!
    have hR : (C ((2 : ℚ) ^ 36) * S2057Psi5Q).natDegree ≤ 12 := by
      rw [Polynomial.natDegree_C_mul (by norm_num)]
      exact s2289Psi5_natDegree.le
    have hcard : ((Finset.range 13).image (fun n : ℕ => (n : ℚ))).card = 13 := by
      rw [Finset.card_image_of_injective]
      · simp
      · intro a b h
        exact Nat.cast_injective h
    rw [hcard]
    have hmax : max (S2132Psi5Z.map (Int.castRingHom ℚ)).natDegree
        (C ((2 : ℚ) ^ 36) * S2057Psi5Q).natDegree ≤ 12 := max_le hL hR
    omega

#check S2003Psi5Z_model
#print axioms S2003Psi5Z_model
end LeanFormal.IUT.XiFPaper.S2003Psi5ModelActual
end