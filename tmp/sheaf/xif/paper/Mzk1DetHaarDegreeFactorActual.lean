/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # #10: det-Haar degree factor data (field-level, no hardcode) -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LeanFormal.IUT.XiFPaper.Mzk1DetHaarDegreeFactorActual

/-- Degree/det-Haar factor between the base-completion tensor and the root product:
`c = ‖det B‖` as an ENNReal scaling. -/
structure DetHaarDegreeFactor where
  detB : ℝ
  c : ℝ≥0∞
  c_eq : c = ENNReal.ofReal (|detB|)

theorem DetHaarDegreeFactor.c_eq_ofReal (D : DetHaarDegreeFactor) :
    D.c = ENNReal.ofReal (|D.detB|) := D.c_eq

theorem DetHaarDegreeFactor.c_pos (D : DetHaarDegreeFactor) (h : D.detB ≠ 0) :
    0 < D.c := by
  rw [D.c_eq]
  exact ENNReal.ofReal_pos.mpr (abs_pos.mpr h)

theorem DetHaarDegreeFactor.c_ne_top (D : DetHaarDegreeFactor) : D.c ≠ ⊤ := by
  rw [D.c_eq]
  exact ENNReal.ofReal_ne_top

theorem DetHaarDegreeFactor.c_eq_one_iff (D : DetHaarDegreeFactor) :
    D.c = 1 ↔ |D.detB| = 1 := by
  rw [D.c_eq, ENNReal.ofReal_eq_one]

theorem DetHaarDegreeFactor.c_le_one_iff (D : DetHaarDegreeFactor) :
    D.c ≤ 1 ↔ |D.detB| ≤ 1 := by
  rw [D.c_eq, ENNReal.ofReal_le_one]

structure DetHaarTransportData (M : Type*) [AddCommGroup M] [MeasurableSpace M] where
  μ : Measure M
  ν : Measure M
  factor : DetHaarDegreeFactor
  transport_eq : ν = factor.c • μ

theorem DetHaarTransportData.apply (M : Type*) [AddCommGroup M] [MeasurableSpace M]
    (D : DetHaarTransportData M) (s : Set M) :
    D.ν s = D.factor.c * D.μ s := by
  rw [D.transport_eq, Measure.smul_apply, smul_eq_mul]

def DetHaarDegreeFactorRequired : Prop := Nonempty DetHaarDegreeFactor

end LeanFormal.IUT.XiFPaper.Mzk1DetHaarDegreeFactorActual
