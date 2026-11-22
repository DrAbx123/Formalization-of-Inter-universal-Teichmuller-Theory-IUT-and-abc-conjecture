import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual
import tmp.sheaf.xif.paper.S1942PrePsiFiveActual
import tmp.sheaf.xif.paper.S2132D5FactorizationActual

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
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual

namespace ProbH5

example (x : ℚ) : ((10 : ℚ[X])).eval x = 10 := by
  rw [Polynomial.eval_natCast]

example (x : ℚ) : ((10 : ℚ[X])).eval x = 10 := by
  rw [Polynomial.eval_ofNat]

theorem hmodel : S2132Psi5Z.map (Int.castRingHom ℚ) = S2057Psi5Q := by
  apply Polynomial.funext
  intro x
  unfold S2132Psi5Z S2057Psi5Q
  rw [S1942_preΨ_five]
  simp only [WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    S1667Curve_b₂, S1667Curve_b₄, S1667Curve_b₆, S1667Curve_b₈]
  simp only [Polynomial.eval_map, Polynomial.eval₂_add, Polynomial.eval₂_sub,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.eval₂_neg, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_neg,
    Polynomial.eval_natCast, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_zero,
    Polynomial.eval₂_zero, Polynomial.eval₂_one, Polynomial.eval₂_natCast,
    Int.coe_castRingHom, map_ofNat, map_neg, map_one]
  ring_nf

#print axioms hmodel

end ProbH5
