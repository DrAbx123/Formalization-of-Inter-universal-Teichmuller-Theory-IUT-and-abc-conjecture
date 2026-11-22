/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Section 0: branches of an oriented edge -/

namespace LeanFormal.IUT.XiFPaper.Section0BranchActual

inductive Branch
  | source
  | target

def flip : Branch → Branch
  | Branch.source => Branch.target
  | Branch.target => Branch.source

theorem flip_flip (b : Branch) : flip (flip b) = b := by
  cases b <;> rfl

theorem flip_ne (b : Branch) : flip b ≠ b := by
  cases b <;> simp [flip]

theorem flip_injective : Function.Injective flip := by
  intro a b h
  cases a <;> cases b <;> simp_all [flip]

theorem flip_surjective : Function.Surjective flip := by
  intro b
  exact ⟨flip b, flip_flip b⟩

end LeanFormal.IUT.XiFPaper.Section0BranchActual
