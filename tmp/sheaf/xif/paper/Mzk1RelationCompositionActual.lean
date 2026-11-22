/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Hodge theater links: relation-composition laws -/

namespace LeanFormal.IUT.XiFPaper.RelationCompositionActual

variable {α : Type*}

def relComp (r s : α → α → Prop) (a c : α) : Prop := ∃ b : α, r a b ∧ s b c

theorem relComp_assoc (r s t : α → α → Prop) :
    relComp (relComp r s) t = relComp r (relComp s t) := by
  funext a c
  apply propext
  constructor
  · rintro ⟨b, ⟨d, h1, h2⟩, h3⟩
    exact ⟨d, h1, b, h2, h3⟩
  · rintro ⟨d, h1, b, h2, h3⟩
    exact ⟨b, ⟨d, h1, h2⟩, h3⟩

def relId (a b : α) : Prop := a = b

theorem relComp_id_left (r : α → α → Prop) :
    relComp relId r = r := by
  funext a c
  apply propext
  constructor
  · rintro ⟨b, hab, hbc⟩
    subst hab
    exact hbc
  · intro h
    exact ⟨a, rfl, h⟩

theorem relComp_id_right (r : α → α → Prop) :
    relComp r relId = r := by
  funext a c
  apply propext
  constructor
  · rintro ⟨b, hab, hbc⟩
    subst hbc
    exact hab
  · intro h
    exact ⟨c, h, rfl⟩

theorem relComp_mono {r r' s s' : α → α → Prop}
    (hr : ∀ a b, r a b → r' a b) (hs : ∀ a b, s a b → s' a b) :
    ∀ a c, relComp r s a c → relComp r' s' a c := by
  rintro a c ⟨b, h1, h2⟩
  exact ⟨b, hr _ _ h1, hs _ _ h2⟩

end LeanFormal.IUT.XiFPaper.RelationCompositionActual
