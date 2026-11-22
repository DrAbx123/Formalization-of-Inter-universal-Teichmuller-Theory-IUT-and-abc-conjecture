import tmp.sheaf.xif.paper.S2482OrderTwoAlgAutClassificationActualV3

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2482WeightZeroConstantActual

open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiCurveActual
open LeanFormal.IUT.XiFPaper.S2482OrderTwoAlgAutClassificationActualV3
open Polynomial

theorem d_eq_zero_mem_range (a : A) (h : d a = 0) :
    ∃ c : F, a = Polynomial.aeval (xC : A) (Polynomial.C c) := by
  obtain ⟨P, Q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq a
  change d (P • (1 : A) + Q • yC) = 0 at h
  rw [d_smul_basis] at h
  have hP : 2 • P.degree ≤ (0 : WithBot ℕ) := by
    rw [← h]
    exact le_max_left _ _
  have hQ : 2 • Q.degree + 3 ≤ (0 : WithBot ℕ) := by
    rw [← h]
    exact le_max_right _ _
  have hQ0 : Q = 0 := by
    by_contra hQne
    have hQdeg : (0 : WithBot ℕ) ≤ Q.degree :=
      (Polynomial.zero_le_degree_iff).mpr hQne
    have hQ2 : (0 : WithBot ℕ) ≤ 2 • Q.degree := by
      exact nsmul_nonneg hQdeg 2
    have h3 : (3 : WithBot ℕ) ≤ 2 • Q.degree + 3 := by
      simpa [add_comm] using add_le_add_right hQ2 3
    exact (not_le_of_gt (lt_of_lt_of_le (by norm_num) h3)) hQ
  have hPdeg : P.degree ≤ (0 : WithBot ℕ) := by
    by_contra hnot
    have hpos : (0 : WithBot ℕ) < P.degree := lt_of_not_ge hnot
    have h2pos : (0 : WithBot ℕ) < 2 • P.degree := by
      simpa using nsmul_lt_nsmul_of_pos hpos (m := 0) (n := 2) (by norm_num)
    exact (not_le_of_gt h2pos) hP
  have hPc : P = Polynomial.C (P.coeff 0) := by
    exact Polynomial.eq_C_of_degree_le_zero hPdeg
  refine ⟨P.coeff 0, ?_⟩
  rw [hQ0, zero_smul, add_zero, hPc]
  rw [Polynomial.aeval_C]
  rw [Polynomial.coeff_C_zero]
  rw [Algebra.smul_def, mul_one]
  rw [IsScalarTower.algebraMap_apply F (Polynomial F) A]
  simp

#check d_eq_zero_mem_range
#print axioms d_eq_zero_mem_range

end LeanFormal.IUT.XiFPaper.S2482WeightZeroConstantActual
end