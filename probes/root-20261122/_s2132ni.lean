import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual
import tmp.sheaf.xif.paper.S1942PrePsiFiveActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 40000000
set_option maxRecDepth 10000
open Polynomial
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S1942PrePsiFiveActual
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual

namespace ProbNI

theorem S2132Psi5Q_eval_zero : S2057Psi5Q.eval 0 = (3814697265625 / 68719476736 : ℚ) := by
  unfold S2057Psi5Q
  rw [S1942_preΨ_five]
  simp only [WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    S1667Curve_b₂, S1667Curve_b₄, S1667Curve_b₆, S1667Curve_b₈]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_neg,
    Polynomial.eval_ofNat, Polynomial.eval_natCast, Polynomial.eval_one, Polynomial.eval_zero]
  ring_nf

theorem S2132NoIntegerModel :
    ¬ ∃ P : ℤ[X], P.map (Int.castRingHom ℚ) = S2057Psi5Q := by
  rintro ⟨P, hP⟩
  have h0 := congrArg (Polynomial.eval (0 : ℚ)) hP
  rw [Polynomial.eval_zero_map, S2132Psi5Q_eval_zero, Int.coe_castRingHom] at h0
  have hz : ((P.eval 0 : ℤ) : ℚ) * 68719476736 = 3814697265625 := by
    rw [h0]
    norm_num
  have hzZ : (P.eval 0 : ℤ) * 68719476736 = 3814697265625 := by
    exact_mod_cast hz
  have heven : (2 : ℤ) ∣ (P.eval 0) * 68719476736 :=
    dvd_mul_of_dvd_right (by norm_num : (2 : ℤ) ∣ 68719476736) _
  rw [hzZ] at heven
  norm_num at heven

#print axioms S2132Psi5Q_eval_zero
#print axioms S2132NoIntegerModel

end ProbNI
