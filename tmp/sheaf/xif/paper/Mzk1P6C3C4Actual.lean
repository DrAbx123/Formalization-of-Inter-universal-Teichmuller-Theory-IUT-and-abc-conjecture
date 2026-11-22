import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P6C3C4Actual
/-- Route §5.4: `kappa=(l+1)/4`. -/
def kappa (l : Real) : Real := (l + 1) / 4
/-- Route §5.4: `c_l=(1/6)(1-12/l^2)`. -/
def cL (l : Real) : Real := (1 / 6) * (1 - 12 / l ^ 2)
/-- C3 upper sandwich plus P5 lower and theta<=H_pkt gives C4: `c_l Q <= A`. -/
theorem c3_to_c4 {l A Q M Hpkt theta : Real}
    (hkappa : 0 < kappa l)
    (hP5 : -M ≤ theta) (htheta : theta ≤ Hpkt)
    (hC3 : Hpkt ≤ kappa l * (A - cL l * Q) - M) :
    cL l * Q ≤ A := by
  have hmain : (0 : Real) ≤ kappa l * (A - cL l * Q) := by linarith
  have hdiff : 0 ≤ A - cL l * Q := (mul_nonneg_iff_of_pos_left hkappa).mp hmain
  linarith
/-- C4 in the displayed `Q/6 <= A + (2/l^2)Q` form. -/
theorem c4_display {l A Q : Real} (hl : l ≠ 0) :
    cL l * Q ≤ A ↔ (1 / 6) * Q ≤ A + (2 / l ^ 2) * Q := by
  have hl2 : l ^ 2 ≠ 0 := pow_ne_zero 2 hl
  have hkey : cL l * Q = (1 / 6) * Q - (2 / l ^ 2) * Q := by
    unfold cL
    field_simp [hl2]
    ring
  constructor <;> intro h <;> linarith [hkey, h]

#print axioms c3_to_c4
#print axioms c4_display
end LeanFormal.IUT.XiFPaper.Mzk1P6C3C4Actual
end