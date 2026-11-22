import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual
import tmp.sheaf.xif.paper.S1942PrePsiFiveActual
open Polynomial
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S1942PrePsiFiveActual
noncomputable def PZ : ℤ[X] :=
  C 3814697265625 + C 97656250000000 * X^2 + C (-133437500000000) * X^3 +
  C (-50580000000000) * X^4 + C 165057216000000 * X^5 + C 96445440000000 * X^6 +
  C (-89948160000000) * X^7 + C (-27525120000000) * X^8 +
  C (-10234101760000) * X^9 + C (-7322650804224) * X^10 +
  C 1309965025280 * X^11 + C 343597383680 * X^12
set_option maxHeartbeats 20000000 in
example : PZ.map (Int.castRingHom ℚ) = S2057Psi5Q := by
  unfold S2057Psi5Q PZ
  rw [S1942_preΨ_five]
  simp only [WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃, S1667Curve, WeierstrassCurve.Δ]
  norm_num
  ring_nf
