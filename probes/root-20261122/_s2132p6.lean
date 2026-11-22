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
open LeanFormal.IUT.XiFPaper.S2126Mod29IntegrationActual

namespace Prob2132e

theorem hmodel : S2132Psi5Z.map (Int.castRingHom ℚ) = S2057Psi5Q := by
  apply Polynomial.funext
  intro x
  unfold S2132Psi5Z S2057Psi5Q
  rw [S1942_preΨ_five]
  simp only [WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    S1667Curve_b₂, S1667Curve_b₄, S1667Curve_b₆, S1667Curve_b₈]
  simp only [Polynomial.eval_map]
  ring_nf

noncomputable def F2Z : ℤ[X] := 19 + 24 * X + 4 * X^2

noncomputable def F10Z : ℤ[X] :=
  10 + 24 * X + 16 * X^2 + 14 * X^3 + 24 * X^4 + 8 * X^5 + 5 * X^6 + 7 * X^7 + 25 * X^9 + X^10

noncomputable def QZ : ℤ[X] :=
  131541285015 + (-24) * X + 3367456896520 * X^2 +
    (-4601293103474) * X^3 + (-1744137931064) * X^4 +
    5691628137904 * X^5 + 3325704827573 * X^6 +
    (-3101660689665) * X^7 + (-949142068972) * X^8 +
    (-352900060707) * X^9 + (-252505200167) * X^10 +
    45171207764 * X^11 + 11848185644 * X^12

theorem integer_identity : S2132Psi5Z = F2Z * F10Z + 29 * QZ := by
  unfold S2132Psi5Z F2Z F10Z QZ
  simp only [map_ofNat, map_neg]
  ring

theorem product_map :
    F2Z.map (Int.castRingHom (ZMod 29)) * F10Z.map (Int.castRingHom (ZMod 29)) =
      S2132Psi5Z.map (Int.castRingHom (ZMod 29)) := by
  have h := congrArg (Polynomial.map (Int.castRingHom (ZMod 29))) integer_identity
  simp only [Polynomial.map_add, Polynomial.map_mul] at h
  rw [h]
  have h29 : ((29 : ℤ[X]).map (Int.castRingHom (ZMod 29))) = 0 := by
    simp
  rw [h29, zero_mul, add_zero]

theorem F10Z_map_eq_f : F10Z.map (Int.castRingHom (ZMod 29)) = S2126Mod29IntegrationActual.f := by
  unfold F10Z S2126Mod29IntegrationActual.f
  simp only [map_ofNat, map_neg, map_one]
  simp only [Polynomial.monomial_eq_C_mul_X]
  ring

theorem factor2_irreducible :
    Irreducible ((19 : (ZMod 29)[X]) + 24 * X + 4 * X^2) := by
  have hg_assoc : Associated (((19 : (ZMod 29)[X]) + 24 * X + 4 * X^2))
      ((12 : (ZMod 29)[X]) + 6 * X + X^2) := by
    have h4 : IsUnit ((4 : (ZMod 29)[X])) := by
      rw [show ((4 : (ZMod 29)[X])) = C (4 : ZMod 29) from (map_ofNat C 4).symm]
      exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by norm_num))
    have h := Associated.associated_unit_mul_left
      ((12 : (ZMod 29)[X]) + 6 * X + X^2) (4 : (ZMod 29)[X]) h4
    -- h : Associated (4 * g) g
    have h' : ((19 : (ZMod 29)[X]) + 24 * X + 4 * X^2) =
        4 * ((12 : (ZMod 29)[X]) + 6 * X + X^2) := by ring
    rw [h']
    exact h
  refine (hg_assoc.irreducible_iff).mpr ?_
  have hno : ∀ x : ZMod 29, ¬ IsRoot ((12 : (ZMod 29)[X]) + 6 * X + X^2) x := by
    decide
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ hno
  compute_degree

theorem factor2_degree : ((19 : (ZMod 29)[X]) + 24 * X + 4 * X^2).natDegree = 2 := by
  compute_degree

end Prob2132e
