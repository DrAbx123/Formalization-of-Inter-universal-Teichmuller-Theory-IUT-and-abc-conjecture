/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Section0SaturatedLengthChainActual

/-! # Chain: corollaries of saturated length families (inter/MapsTo) -/

namespace LeanFormal.IUT.XiFPaper.Section0SaturatedSetsActual

variable {V E : Type*}

theorem saturated_lengthSet_inter (G : V → V → Prop) (n m : Nat) :
    Saturated G ({p : PathPair V E | pairLength p = n} ∩
      {p : PathPair V E | pairLength p = m}) :=
  saturated_inter G (saturated_lengthSet G n) (saturated_lengthSet G m)

theorem mapsTo_lengthSet (G : V → V → Prop) (n : Nat) {sigma : V → V}
    (hsigma : EdgePreserving G sigma) :
    Set.MapsTo (pairMap sigma) {p : PathPair V E | pairLength p = n}
      {p : PathPair V E | pairLength p = n} :=
  saturated_mapsTo G (saturated_lengthSet G n) hsigma

theorem mapsTo_lengthSet_le (G : V → V → Prop) (n : Nat) {sigma : V → V}
    (hsigma : EdgePreserving G sigma) :
    Set.MapsTo (pairMap sigma) {p : PathPair V E | pairLength p ≤ n}
      {p : PathPair V E | pairLength p ≤ n} :=
  saturated_mapsTo G (saturated_lengthSet_le G n) hsigma

end LeanFormal.IUT.XiFPaper.Section0SaturatedSetsActual
