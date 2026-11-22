/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # A1 determinant: saturation index data -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1SaturationIndexDataActual

/-- One-side saturation index data `log[Λsat:Λ]`. -/
structure SaturationIndexData where
  index : ℕ
  logIndex : ℝ
  logIndex_eq : logIndex = Real.log (index : ℝ)
  one_le_index : 1 ≤ index

theorem SaturationIndexData.logIndex_nonneg (D : SaturationIndexData) :
    0 ≤ D.logIndex := by
  rw [D.logIndex_eq]
  exact Real.log_nonneg (by exact_mod_cast D.one_le_index)

/-- Two-sided determinant comparison: F-side and K-side saturation indices. -/
structure TwoSidedSaturationData extends SaturationIndexData where
  kIndex : ℕ
  kLogIndex : ℝ
  kLogIndex_eq : kLogIndex = Real.log (kIndex : ℝ)
  k_one_le : 1 ≤ kIndex

theorem TwoSidedSaturationData.kLogIndex_nonneg (D : TwoSidedSaturationData) :
    0 ≤ D.kLogIndex := by
  rw [D.kLogIndex_eq]
  exact Real.log_nonneg (by exact_mod_cast D.k_one_le)

theorem TwoSidedSaturationData.logIndex_mono (D : TwoSidedSaturationData)
    (h : D.index ≤ D.kIndex) : D.logIndex ≤ D.kLogIndex := by
  rw [D.logIndex_eq, D.kLogIndex_eq]
  exact Real.log_le_log (by positivity) (by exact_mod_cast h)

noncomputable def TwoSidedSaturationData.detLogIndex (D : TwoSidedSaturationData) : ℝ :=
  D.kLogIndex - D.logIndex

theorem TwoSidedSaturationData.detLogIndex_nonneg (D : TwoSidedSaturationData)
    (h : D.index ≤ D.kIndex) : 0 ≤ D.detLogIndex := by
  unfold TwoSidedSaturationData.detLogIndex
  linarith [D.logIndex_mono h]

end LeanFormal.IUT.XiFPaper.Mzk1SaturationIndexDataActual
