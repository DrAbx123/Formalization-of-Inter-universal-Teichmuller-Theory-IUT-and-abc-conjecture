/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # A1: saturation index as determinant of integral bases -/
noncomputable section
open Module
namespace LeanFormal.IUT.XiFPaper.Mzk1LatticeSaturationIndexActual

theorem saturation_relIndex_eq_natAbs_det {E : Type*} [AddCommGroup E]
    (L₁ L₂ : AddSubgroup E) (H : L₁ ≤ L₂) {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b₁ : Module.Basis ι ℤ L₁.toIntSubmodule) (b₂ : Module.Basis ι ℤ L₂.toIntSubmodule) :
    L₁.relIndex L₂ =
      (b₂.det (fun i => ⟨b₁ i, H (SetLike.coe_mem _)⟩)).natAbs :=
  AddSubgroup.relIndex_eq_natAbs_det L₁ L₂ H b₁ b₂

/-- Log of the saturation index `[L₂ : L₁]` (A1 determinant side). -/
noncomputable def saturationLogIndex {E : Type*} [AddCommGroup E]
    (L₁ L₂ : AddSubgroup E) : ℝ :=
  Real.log (L₁.relIndex L₂ : ℝ)

theorem saturationLogIndex_eq_log_natAbs_det {E : Type*} [AddCommGroup E]
    (L₁ L₂ : AddSubgroup E) (H : L₁ ≤ L₂) {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b₁ : Module.Basis ι ℤ L₁.toIntSubmodule) (b₂ : Module.Basis ι ℤ L₂.toIntSubmodule)
    (hpos : L₁.relIndex L₂ ≠ 0) :
    saturationLogIndex L₁ L₂ =
      Real.log ((b₂.det (fun i => ⟨b₁ i, H (SetLike.coe_mem _)⟩)).natAbs : ℝ) := by
  unfold saturationLogIndex
  rw [saturation_relIndex_eq_natAbs_det L₁ L₂ H b₁ b₂]

end LeanFormal.IUT.XiFPaper.Mzk1LatticeSaturationIndexActual
