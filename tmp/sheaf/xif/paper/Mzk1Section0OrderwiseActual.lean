/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Section 0: orderwise connected subsets -/

namespace LeanFormal.IUT.XiFPaper.Section0OrderwiseActual

variable {α : Type*} [Preorder α]

def OrderwiseConnected (S : Set α) : Prop :=
  ∀ ⦃c : α⦄, (∃ a ∈ S, a < c) → (∃ b ∈ S, c < b) → c ∈ S

theorem orderwiseConnected_univ : OrderwiseConnected (Set.univ : Set α) := by
  intro c h1 h2
  exact Set.mem_univ c

theorem orderwiseConnected_Icc [LinearOrder α] (a b : α) :
    OrderwiseConnected (Set.Icc a b) := by
  intro c h1 h2
  obtain ⟨x, hx, hxc⟩ := h1
  obtain ⟨y, hy, hcy⟩ := h2
  exact ⟨le_trans hx.1 (le_of_lt hxc), le_trans (le_of_lt hcy) hy.2⟩

theorem orderwiseConnected_Icc_self [LinearOrder α] (a : α) :
    OrderwiseConnected (Set.Icc a a) := orderwiseConnected_Icc a a

end LeanFormal.IUT.XiFPaper.Section0OrderwiseActual
