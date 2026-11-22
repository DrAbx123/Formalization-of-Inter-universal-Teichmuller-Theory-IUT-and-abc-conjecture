/- Route F1: the named Cech-model line-bundle data for height transport (cover, transition
unit, compatible H0 frames).  B3 consumes this directly; the omega_Y(E) instance is built by
supplying the cover/unit from Mzk1G1A5LineBundleIsoActual and the frames from the height
normalization. -/
import tmp.sheaf.xif.paper.Mzk1G1A5LineBundleIsoActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F1HeightTransportActual

open LeanFormal.IUT.XiFPaper.Mzk1G1A5LineBundleIsoActual

/-- Cech-model data for route F1 (height transport): a two-chart cover, the line-bundle
transition unit, and H0 frames on the two charts compatible over the overlap. -/
structure F1HeightTransportData (n : Nat) where
  cover : TwoChartCech.Cover ℚ
  transitionUnit : cover.A01ˣ
  frame0 : cover.A0
  frame1 : cover.A1
  frame_compat : cover.ρ0 frame0 = (transitionUnit : cover.A01) * cover.ρ1 frame1

/-- The trivial Cech cover over Q (all charts Q, restrictions the identity). -/
def trivialCover : TwoChartCech.Cover ℚ where
  A0 := ℚ
  A1 := ℚ
  A01 := ℚ
  ρ0 := Algebra.ofId ℚ ℚ
  ρ1 := Algebra.ofId ℚ ℚ

/-- The trivial F1 height-transport data (unit and frames all 1), exhibiting that the
interface is inhabited. -/
def trivialF1HeightTransportData (n : Nat) : F1HeightTransportData n := by
  refine ⟨trivialCover, 1, 1, 1, ?_⟩
  show (1 : ℚ) = 1 * 1
  ring

theorem f1HeightTransportData_nonempty (n : Nat) : Nonempty (F1HeightTransportData n) :=
  ⟨trivialF1HeightTransportData n⟩

/-- The H0-frame condition is exactly the line-bundle H0 condition from the donor. -/
theorem f1_frame_mem_H0 (n : Nat) (D : F1HeightTransportData n) :
    (D.frame0, D.frame1) ∈ (D.cover.lineBundle D.transitionUnit).H0 ↔
      D.cover.ρ0 D.frame0 = (D.transitionUnit : D.cover.A01) * D.cover.ρ1 D.frame1 :=
  D.cover.mem_H0_lineBundle_iff D.transitionUnit (D.frame0, D.frame1)

#print axioms trivialF1HeightTransportData
#print axioms f1_frame_mem_H0
end LeanFormal.IUT.XiFPaper.Mzk1G1F1HeightTransportActual

