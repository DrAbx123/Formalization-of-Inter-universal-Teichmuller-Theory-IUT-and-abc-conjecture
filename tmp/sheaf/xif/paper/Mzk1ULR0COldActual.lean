/- R0 (route alignment 2026-11-18): c_old vs c_P distinction.
   Step (1): general normalized log formula at the qVFamily generator,
     log||q_P|| = -(v_P(q_P) * log N(P)) / [F_P:Q_p],
   with N(P)=p^f, [F_P:Q_p]=e*f, derives -log_p ||q_P|| = v_P(q_P)/e_P^abs.
   Step (2): c_old = v_P * f, c_P = v_P/e, hence c_old = e*f*c_P (same P|p).
   c_old = c_P only when e*f = 1; NOT assumed generally.
   Step (3): fiber crosswalk cPFullFiber_b = thetaLamWeight_b * cP_local_b is separate.
   No normRatio=1 claim. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULR0COldActual

/-- Route R0 step (1): normalized log formula + N(P)=p^f + [F_P:Q_p]=e*f
    implies -log_p ||q_P|| = v_P(q_P)/e_P^abs. -/
theorem neg_log_norm_eq_order_div_e
    (p logNorm v e f : Real)
    (hp0 : 0 < p) (hp1 : p ≠ 1)
    (he : e ≠ 0) (hf : f ≠ 0)
    (hformula : logNorm = -(v * (f * Real.log p)) / (e * f)) :
    -(logNorm / Real.log p) = v / e := by
  have hlogp : Real.log p ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hp0 hp1
  rw [hformula]
  field_simp [hlogp, he, hf]

/-- Route R0 step (2): c_old = v_P * f (same P|p) and c_P = v_P / e
    imply c_old = e * f * c_P. -/
theorem cOld_eq_ef_mul_cP
    (v e f cOld cP : Real)
    (he : e ≠ 0)
    (hcOld : cOld = v * f)
    (hcP : cP = v / e) :
    cOld = e * f * cP := by
  rw [hcOld, hcP]
  field_simp [he]

/-- Route R0 step (2'): the old normalization and paper c_P agree iff e*f = 1
    (given v ≠ 0). -/
theorem cOld_eq_cP_iff_ef_one
    (v e f cOld cP : Real)
    (he : e ≠ 0) (hv : v ≠ 0)
    (hcOld : cOld = v * f)
    (hcP : cP = v / e) :
    cOld = cP ↔ e * f = 1 := by
  rw [hcOld, hcP, eq_div_iff he]
  constructor
  · intro h
    have h'' : v * (f * e) = v * 1 := by
      rw [← mul_assoc, h, mul_one]
    simpa [mul_comm] using mul_left_cancel₀ hv h''
  · intro h
    have h' : f * e = 1 := by rw [mul_comm]; exact h
    calc v * f * e = v * (f * e) := by ring
      _ = v * 1 := by rw [h']
      _ = v := by ring

#print axioms neg_log_norm_eq_order_div_e
#print axioms cOld_eq_ef_mul_cP
#print axioms cOld_eq_cP_iff_ef_one

end LeanFormal.IUT.XiFPaper.Mzk1ULR0COldActual