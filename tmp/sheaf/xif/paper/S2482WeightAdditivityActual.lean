import tmp.sheaf.xif.paper.S2482OrderTwoAlgAutClassificationActual_v2

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2482WeightAdditivityActual

open LeanFormal.IUT.XiFPaper.S2482OrderTwoAlgAutClassificationActualV2
open Polynomial

lemma two_nsmul_max' (a b : WithBot ℕ) :
    2 • max a b = max (2 • a) (2 • b) := by
  rw [two_nsmul, two_nsmul, two_nsmul]
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (add_le_add h h)]
  · rw [max_eq_left h, max_eq_left (add_le_add h h)]

lemma max_add_three' (a b : WithBot ℕ) :
    max a b + 3 = max (a + 3) (b + 3) := by
  rcases le_total a b with h | h
  · have h3 : a + 3 ≤ b + 3 := by
      simpa [add_comm] using add_le_add_right h 3
    rw [max_eq_right h, max_eq_right h3]
  · have h3 : b + 3 ≤ a + 3 := by
      simpa [add_comm] using add_le_add_right h 3
    rw [max_eq_left h, max_eq_left h3]

lemma two_nsmul_degree_add_le (p q : Poly) :
    2 • (p + q).degree ≤ max (2 • p.degree) (2 • q.degree) := by
  calc 2 • (p + q).degree
      ≤ 2 • max p.degree q.degree := by
        exact nsmul_le_nsmul_right (Polynomial.degree_add_le p q) 2
    _ = max (2 • p.degree) (2 • q.degree) := two_nsmul_max' _ _

lemma two_nsmul_degree_add_le_three (p q : Poly) :
    2 • (p + q).degree + 3 ≤
      max (2 • p.degree + 3) (2 • q.degree + 3) := by
  calc 2 • (p + q).degree + 3
      ≤ 2 • max p.degree q.degree + 3 := by
        simpa [add_comm] using add_le_add_right
          (nsmul_le_nsmul_right (Polynomial.degree_add_le p q) 2) 3
    _ = max (2 • p.degree + 3) (2 • q.degree + 3) := by
        rw [two_nsmul_max', max_add_three']

lemma W_add_le (z w : A) : W (z + w) ≤ max (W z) (W w) := by
  rw [W_eq, W_eq, W_eq, coords_add]
  set p1 := (coords z).1
  set q1 := (coords z).2
  set p2 := (coords w).1
  set q2 := (coords w).2
  change max (2 • (p1 + p2).degree) (2 • (q1 + q2).degree + 3) ≤
    max (max (2 • p1.degree) (2 • q1.degree + 3))
      (max (2 • p2.degree) (2 • q2.degree + 3))
  refine max_le ?_ ?_
  · refine (two_nsmul_degree_add_le p1 p2).trans ?_
    refine max_le ?_ ?_
    · exact le_trans (le_max_left _ _) (le_max_left _ _)
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · refine (two_nsmul_degree_add_le_three q1 q2).trans ?_
    refine max_le ?_ ?_
    · exact le_trans (le_max_right _ _) (le_max_left _ _)
    · exact le_trans (le_max_right _ _) (le_max_right _ _)


end LeanFormal.IUT.XiFPaper.S2482WeightAdditivityActual
end