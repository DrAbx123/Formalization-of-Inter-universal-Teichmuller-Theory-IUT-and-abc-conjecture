/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1LatticeSaturationIndexActual
import Mathlib.Tactic

/-! # A1: two-sided saturation bases package for stage4 lattice comparison -/
noncomputable section
open Module
namespace LeanFormal.IUT.XiFPaper.Mzk1SaturationBasesDataActual
open LeanFormal.IUT.XiFPaper.Mzk1LatticeSaturationIndexActual

structure SaturationBasesData (E : Type*) [AddCommGroup E] where
  L₁ : AddSubgroup E
  L₂ : AddSubgroup E
  le : L₁ ≤ L₂
  ι : Type
  [fintype : Fintype ι]
  [decidableEq : DecidableEq ι]
  b₁ : Module.Basis ι ℤ L₁.toIntSubmodule
  b₂ : Module.Basis ι ℤ L₂.toIntSubmodule
  relIndex_ne_zero : L₁.relIndex L₂ ≠ 0

theorem SaturationBasesData.saturationLogIndex_eq {E : Type*} [AddCommGroup E]
    (D : SaturationBasesData E) [Fintype D.ι] [DecidableEq D.ι] :
    saturationLogIndex D.L₁ D.L₂ =
      Real.log ((D.b₂.det (fun i => ⟨D.b₁ i, D.le (SetLike.coe_mem _)⟩)).natAbs : ℝ) := by
  exact saturationLogIndex_eq_log_natAbs_det D.L₁ D.L₂ D.le D.b₁ D.b₂ D.relIndex_ne_zero

end LeanFormal.IUT.XiFPaper.Mzk1SaturationBasesDataActual
