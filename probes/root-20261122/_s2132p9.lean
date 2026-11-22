import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual
import tmp.sheaf.xif.paper.S1942PrePsiFiveActual
import tmp.sheaf.xif.paper.S2132D5FactorizationActual
import tmp.sheaf.xif.paper.S2126Mod29IntegrationActual

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

namespace Prob2132h

noncomputable def F10Z : ℤ[X] :=
  10 + 24 * X + 16 * X^2 + 14 * X^3 + 24 * X^4 + 8 * X^5 + 5 * X^6 + 7 * X^7 + 25 * X^9 + X^10

noncomputable def F2Z : ℤ[X] := 19 + 24 * X + 4 * X^2

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
    rw [show ((29 : ℤ[X])) = ((29 : ℕ) : ℤ[X]) from by norm_num]
    rw [Polynomial.map_natCast]
    exact CharP.cast_eq_zero ((ZMod 29)[X]) 29
  rw [h29, zero_mul, add_zero]

-- F10 identification attempts
example : F10Z.map (Int.castRingHom (ZMod 29)) = f := by
  unfold F10Z f
  simp only [map_ofNat]
  ring

example : F2Z.map (Int.castRingHom (ZMod 29)) =
    ((19 : (ZMod 29)[X]) + 24 * X + 4 * X^2) := by
  unfold F2Z
  simp only [map_ofNat]
  ring

theorem corrected_product :
    ((19 : (ZMod 29)[X]) + 24 * X + 4 * X^2) * f =
      S2132Psi5Z.map (Int.castRingHom (ZMod 29)) := by
  have h10 : F10Z.map (Int.castRingHom (ZMod 29)) = f := by
    unfold F10Z f
    simp only [map_ofNat]
    ring
  have h2 : F2Z.map (Int.castRingHom (ZMod 29)) =
      ((19 : (ZMod 29)[X]) + 24 * X + 4 * X^2) := by
    unfold F2Z
    simp only [map_ofNat]
    ring
  rw [← h10, ← h2]
  exact product_map

theorem factorProduct_ne :
    S2132Factor2 * S2132Factor10 ≠
      S2132Psi5Z.map (Int.castRingHom (ZMod 29)) := by
  intro h
  have h0 := congrArg (Polynomial.eval (0 : ZMod 29)) h
  simp [S2132Factor2, S2132Factor10, S2132Psi5Z, f] at h0
  norm_num at h0

end Prob2132h
