import tmp.sheaf.xif.paper.S2132D5FactorizationActual
import tmp.sheaf.xif.paper.S2126Mod29IntegrationActual
import tmp.sheaf.xif.paper.S2126Mod29IntegrationActual
open Polynomial
noncomputable section
set_option maxHeartbeats 40000000
noncomputable def F10Z : ℤ[X] :=
  10 + 24 * X + 16 * X^2 + 14 * X^3 + 24 * X^4 + 8 * X^5 + 5 * X^6 + 7 * X^7 + 25 * X^9 + X^10
example : F10Z.map (Int.castRingHom (ZMod 29)) = f := by
  unfold F10Z f
  norm_num [Polynomial.monomial_eq_C_mul_X]
  ring
