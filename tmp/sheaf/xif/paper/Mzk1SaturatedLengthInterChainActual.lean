/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1SaturatedLengthCorollariesActual

/-! # Chain: MapsTo for intersections of saturated length families -/

namespace LeanFormal.IUT.XiFPaper.Section0SaturatedSetsActual

variable {V E : Type*}

theorem mapsTo_lengthSet_inter (G : V → V → Prop) (n m : Nat) {sigma : V → V}
    (hsigma : EdgePreserving G sigma) :
    Set.MapsTo (pairMap sigma)
      ({p : PathPair V E | pairLength p = n} ∩
        {p : PathPair V E | pairLength p = m})
      ({p : PathPair V E | pairLength p = n} ∩
        {p : PathPair V E | pairLength p = m}) :=
  saturated_mapsTo G (saturated_lengthSet_inter G n m) hsigma

theorem saturated_lengthSet_univ_inter (G : V → V → Prop) (n : Nat) :
    Saturated G ({p : PathPair V E | pairLength p = n} ∩ Set.univ) :=
  saturated_inter G (saturated_lengthSet G n) (saturated_univ G)

end LeanFormal.IUT.XiFPaper.Section0SaturatedSetsActual
