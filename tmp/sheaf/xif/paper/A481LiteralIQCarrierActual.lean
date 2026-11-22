/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.PadicLogShellModel

/-! # A481 literal IQ carrier: restricted product of local log-shells -/

set_option linter.unusedSectionVars false

namespace LeanFormal.IUT.IQCarrier

open Metric Set

universe u

variable (ι : Type u) [Fintype ι] (p : Nat) [Fact p.Prime]

/-- The literal IQ carrier over the finite place set: the restricted product of the
local p-adic log-shell models at each place. -/
abbrev LiteralIQCarrier (ι : Type u) (p : Nat) [Fact p.Prime] : Type u := ι → ℚ_[p]

/-- The unit region O: the product of the local unit balls. -/
noncomputable def unitRegion : Set (LiteralIQCarrier ι p) :=
  {x | ∀ v : ι, x v ∈ closedBall (0 : ℚ_[p]) (1 : ℝ)}

/-- The scaling action lambda . (-): translation by the chosen place family. -/
noncomputable def scale (lam : ι → ℚ_[p]) (x : LiteralIQCarrier ι p) : LiteralIQCarrier ι p :=
  fun v => lam v + x v

/-- The scaled unit region lambda . O. -/
noncomputable def scaledUnitRegion (lam : ι → ℚ_[p]) : Set (LiteralIQCarrier ι p) :=
  scale ι p lam '' unitRegion ι p

theorem mem_unitRegion_iff (x : LiteralIQCarrier ι p) :
    x ∈ unitRegion ι p ↔ ∀ v : ι, x v ∈ closedBall (0 : ℚ_[p]) (1 : ℝ) := Iff.rfl

theorem zero_mem_unitRegion : (0 : LiteralIQCarrier ι p) ∈ unitRegion ι p := by
  rw [mem_unitRegion_iff]
  intro v
  rw [mem_closedBall]
  simp

theorem unitRegion_compact : IsCompact (unitRegion ι p) := by
  have h : unitRegion ι p =
      Set.univ.pi (fun _ : ι => closedBall (0 : ℚ_[p]) (1 : ℝ)) := by
    ext x
    simp [unitRegion]
  rw [h]
  exact isCompact_univ_pi (fun _ => isCompact_closedBall (0 : ℚ_[p]) (1 : ℝ))

theorem scale_apply (lam : ι → ℚ_[p]) (x : LiteralIQCarrier ι p) (v : ι) :
    scale ι p lam x v = lam v + x v := rfl

theorem scale_zero (lam : ι → ℚ_[p]) :
    scale ι p lam (0 : LiteralIQCarrier ι p) = lam := by
  funext v
  simp [scale]

theorem scale_neg_self (lam : ι → ℚ_[p]) :
    scale ι p lam (-lam) = (0 : LiteralIQCarrier ι p) := by
  funext v
  simp [scale]

theorem mem_scaledUnitRegion_iff (lam : ι → ℚ_[p]) (x : LiteralIQCarrier ι p) :
    x ∈ scaledUnitRegion ι p lam ↔
      ∃ o ∈ unitRegion ι p, x = scale ι p lam o := by
  constructor
  · rintro ⟨o, ho, hxo⟩
    exact ⟨o, ho, hxo.symm⟩
  · rintro ⟨o, ho, hxo⟩
    exact ⟨o, ho, hxo.symm⟩

theorem scaledUnitRegion_nonempty (lam : ι → ℚ_[p]) :
    (scaledUnitRegion ι p lam).Nonempty :=
  ⟨scale ι p lam 0, 0, zero_mem_unitRegion ι p, rfl⟩

end LeanFormal.IUT.IQCarrier
