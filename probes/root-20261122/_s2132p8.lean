import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual
import tmp.sheaf.xif.paper.S1942PrePsiFiveActual
import tmp.sheaf.xif.paper.S2132D5FactorizationActual
import tmp.sheaf.xif.paper.S2126Mod29IntegrationActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 40000000
set_option maxRecDepth 10000
open Polynomial
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S1942PrePsiFiveActual
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual

namespace Prob2132g

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
    map_ofNat, map_neg, map_one]
  ring_nf

noncomputable def F10Z : ℤ[X] :=
  10 + 24 * X + 16 * X^2 + 14 * X^3 + 24 * X^4 + 8 * X^5 + 5 * X^6 + 7 * X^7 + 25 * X^9 + X^10

theorem F10Z_map_eq_f : F10Z.map (Int.castRingHom (ZMod 29)) = f := by
  unfold F10Z f
  simp only [map_ofNat, map_neg, map_one]
  simp only [Polynomial.monomial_eq_C_mul_X]
  ring

theorem factorProduct_ne :
    S2132Factor2 * S2132Factor10 ≠
      S2132Psi5Z.map (Int.castRingHom (ZMod 29)) := by
  intro h
  have h0 := congrArg (Polynomial.eval (0 : ZMod 29)) h
  simp [S2132Factor2, S2132Factor10, S2132Psi5Z, S2132Factor10_eq_s2126] at h0
  norm_num at h0

end Prob2132g
