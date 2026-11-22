/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # A1085: structural target objects (containment / determinant morphism) -/

/-
| field | value |
|---|---|
| Status | PARTIAL (both structural targets and their one-step proofs are PROVED; existence of the objects = GAP-XID) |
| 真证 | `target_of_containment`; `target_of_detMorphism` |
| GAP | GAP-XID: no inhabitant of `QPilotThetaContainment` / `QPilotThetaDetMorphism` (this is the Step (xi-d) content) |
| 循环性 | no target assumed; the structural objects are explicit data |
| 坐标 | Haar/signed: qRegion ⊆ θRegion; containment gives -A <= -R |
-/

noncomputable section
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.Mzk1StructuralTargetActual

/-- Structural containment target: two regions with log-volumes -A, -R and q ⊆ θ. -/
structure QPilotThetaContainment (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) (A R : Real) where
  qRegion : Set Ω
  θRegion : Set Ω
  q_measurable : MeasurableSet qRegion
  θ_measurable : MeasurableSet θRegion
  hq_fin : μ qRegion < ⊤
  hθ_fin : μ θRegion < ⊤
  hq_pos : 0 < μ qRegion
  subset : qRegion ⊆ θRegion
  q_norm : -A = Real.log (μ qRegion).toReal
  θ_norm : -R = Real.log (μ θRegion).toReal

/-- **One-step proof**: structural containment gives the target `-A <= -R`. -/
theorem target_of_containment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {A R : Real} (D : QPilotThetaContainment Ω μ A R) :
    -A ≤ -R := by
  have hmono : μ D.qRegion ≤ μ D.θRegion := measure_mono D.subset
  have hq_lt : μ D.qRegion < ⊤ := lt_of_le_of_lt hmono D.hθ_fin
  have hq_pos : 0 < (μ D.qRegion).toReal := ENNReal.toReal_pos D.hq_pos.ne' hq_lt.ne
  have hle : (μ D.qRegion).toReal ≤ (μ D.θRegion).toReal :=
    ENNReal.toReal_mono D.hθ_fin.ne hmono
  have hlog : Real.log (μ D.qRegion).toReal ≤ Real.log (μ D.θRegion).toReal :=
    Real.log_le_log hq_pos hle
  rw [← D.q_norm, ← D.θ_norm] at hlog
  exact hlog

/-- Determinant-morphism target (abstract volume; paper Step (xi-d) shape). -/
structure QPilotThetaDetMorphism (Ω : Type*) (vol : Set Ω → Real) (A R : Real) where
  G : Ω → Ω
  M : Real
  hM : 1 ≤ M
  hchar : vol (G '' qRegion) = M * vol qRegion
  qRegion : Set Ω
  θRegion : Set Ω
  subset_scaled : G '' qRegion ⊆ θRegion
  hmono : ∀ {S T : Set Ω}, S ⊆ T → vol S ≤ vol T
  q_pos : 0 < vol qRegion
  q_norm : -A = Real.log (vol qRegion)
  θ_norm : -R = Real.log (vol θRegion)

/-- **One-step proof (determinant version)**: `-A <= -R`. -/
theorem target_of_detMorphism {Ω : Type*} {vol : Set Ω → Real} {A R : Real}
    (D : QPilotThetaDetMorphism Ω vol A R) : -A ≤ -R := by
  have hq_le : vol D.qRegion ≤ vol D.θRegion := by
    calc vol D.qRegion ≤ D.M * vol D.qRegion := by
          have h := mul_le_mul_of_nonneg_right D.hM D.q_pos.le
          simpa [one_mul] using h
      _ = vol (D.G '' D.qRegion) := D.hchar.symm
      _ ≤ vol D.θRegion := D.hmono D.subset_scaled
  have hlog : Real.log (vol D.qRegion) ≤ Real.log (vol D.θRegion) :=
    Real.log_le_log D.q_pos hq_le
  rw [← D.q_norm, ← D.θ_norm] at hlog
  exact hlog

def structuralTargetRows : List (String × String) :=
  [ ("QPilotThetaContainment", "region containment + two log-volume normalizations") ,
    ("target_of_containment", "-A <= -R (PROVED)") ,
    ("QPilotThetaDetMorphism", "G/M/hchar/subset_scaled/det law (abstract volume)") ,
    ("target_of_detMorphism", "-A <= -R (PROVED)") ,
    ("GAP-XID", "no inhabitant (Step (xi-d) geometric content)") ]

theorem structuralTargetRows_length : structuralTargetRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1StructuralTargetActual