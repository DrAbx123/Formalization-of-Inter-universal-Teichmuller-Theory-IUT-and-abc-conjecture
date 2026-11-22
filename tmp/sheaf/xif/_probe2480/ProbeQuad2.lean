import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
open Polynomial
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual

#check (S2132F2Z.map (Int.castRingHom (ZMod 29)))
#check (C (19 : ZMod 29) + C 24 * X + C 4 * X ^ 2 : (ZMod 29)[X])
#check (show (ZMod 29)[X] from S2132F2Z.map (Int.castRingHom (ZMod 29)))
example : (S2132F2Z.map (Int.castRingHom (ZMod 29))) =
    (C (19 : ZMod 29) + C 24 * X + C 4 * X ^ 2) := by
  simp [S2132F2Z]
example : (S2132F2Z.map (Int.castRingHom (ZMod 29))).natDegree = 2 := by
  rw [show (S2132F2Z.map (Int.castRingHom (ZMod 29))) =
    (C (19 : ZMod 29) + C 24 * X + C 4 * X ^ 2) by simp [S2132F2Z]]
  rw [show (C (19 : ZMod 29) + C 24 * X + C 4 * X ^ 2) =
    (C 4 * X ^ 2 + C 24 * X + C 19) by ring]
  apply Polynomial.natDegree_quadratic
  norm_num
