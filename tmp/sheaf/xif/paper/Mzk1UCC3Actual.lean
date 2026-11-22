import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual
def kappa (l : Real) : Real := (l + 1) / 4
def cL (l : Real) : Real := (1 / 6) * (1 - 12 / l ^ 2)
/-- U-C C3: `H_pkt <= kappa(A-c_l Q)-M`; P5 `-M <= theta <= H_pkt`;
    conclude C4 `c_l Q <= A`. -/
theorem uc_c3_to_c4 {l A Q M Hpkt theta : Real}
    (hkappa : 0 < kappa l)
    (hP5 : -M ≤ theta) (htheta : theta ≤ Hpkt)
    (hC3 : Hpkt ≤ kappa l * (A - cL l * Q) - M) :
    cL l * Q ≤ A := by
  have hmain : (0 : Real) ≤ kappa l * (A - cL l * Q) := by linarith
  have hdiff : 0 ≤ A - cL l * Q := (mul_nonneg_iff_of_pos_left hkappa).mp hmain
  linarith
#print axioms uc_c3_to_c4
end LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual
end