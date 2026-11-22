import tmp.sheaf.xif.paper.S2590Q1249ChainActual
import tmp.sheaf.xif.paper.S2572Bezout134Actual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2572Bezout134Actual
open LeanFormal.IUT.XiFPaper.S2589ProductDActual
open LeanFormal.IUT.XiFPaper.S2590Q1249ChainActual

namespace LeanFormal.IUT.XiFPaper.S2592Bezout1249Actual

abbrev F10 : (ZMod 1249)[X] := S2550F10

lemma S1_eq_rD_sub_X : S1 = rD - X := by
  ext n
  by_cases hn : n ≤ 9
  · interval_cases n <;>
      (simp [S1, rD, Polynomial.coeff_sub, Polynomial.coeff_X] <;> decide)
  · have h1 : S1.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : S1.natDegree ≤ 9 := by unfold S1; compute_degree!
      omega
    have h2 : rD.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : rD.natDegree ≤ 9 := by unfold rD; compute_degree!
      omega
    have hx : (X : (ZMod 1249)[X]).coeff n = 0 := by
      rw [coeff_X, if_neg (by omega)]
    rw [h1, coeff_sub, hx, h2]
    simp

theorem hbez1 : ∃ A B : (ZMod 1249)[X],
    A * F10 + B * ((X : (ZMod 1249)[X]) ^ 1249 - X) = 1 := by
  obtain ⟨q, hq⟩ := chain1249
  refine ⟨A1 - B1 * q, B1, ?_⟩
  have hS : S1 = rD - X := S1_eq_rD_sub_X
  calc
    (A1 - B1 * q) * F10 + B1 * ((X : (ZMod 1249)[X]) ^ 1249 - X)
        = A1 * F10 + B1 * S1 := by
          have hq' : (X : (ZMod 1249)[X]) ^ 1249 - X =
              F10 * q + (rD - X) := by
            rw [← hq]
            ring
          rw [hS, hq']
          ring
    _ = 1 := bezout1

end LeanFormal.IUT.XiFPaper.S2592Bezout1249Actual
end
