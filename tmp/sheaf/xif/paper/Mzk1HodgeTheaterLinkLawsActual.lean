/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Hodge theater links: equivalence-relation law interface -/

namespace LeanFormal.IUT.XiFPaper.HodgeTheaterLinkLawsActual

structure HTLink (α : Type*) where
  rel : α → α → Prop
  refl' : ∀ x : α, rel x x
  symm' : ∀ {x y : α}, rel x y → rel y x
  trans' : ∀ {x y z : α}, rel x y → rel y z → rel x z

variable {α : Type*}

theorem htRelRefl (L : HTLink α) (x : α) : L.rel x x := L.refl' x

theorem htRelSymm (L : HTLink α) {x y : α} (h : L.rel x y) : L.rel y x := L.symm' h

theorem htRelTrans (L : HTLink α) {x y z : α} (h1 : L.rel x y) (h2 : L.rel y z) :
    L.rel x z := L.trans' h1 h2

theorem htRelSymmIff (L : HTLink α) {x y : α} : L.rel x y ↔ L.rel y x := 
  ⟨L.symm', L.symm'⟩

theorem htRelSymmSymm (L : HTLink α) {x y : α} (h : L.rel x y) : L.rel x y := 
  L.symm' (L.symm' h)

theorem htRelTransSymm (L : HTLink α) {x y z : α} (h1 : L.rel x y) (h2 : L.rel z y) :
    L.rel x z := L.trans' h1 (L.symm' h2)

end LeanFormal.IUT.XiFPaper.HodgeTheaterLinkLawsActual
