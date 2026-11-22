/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual
import tmp.sheaf.xif.paper.RootNormalizedContainmentActual
import tmp.sheaf.xif.paper.RootHullMeasureActual
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual
import tmp.sheaf.xif.paper.Ind3OutputHullQPilotActual
import tmp.sheaf.xif.paper.SignedLabelOneActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual
import tmp.sheaf.xif.paper.ThetaTensorScaledImageActual
import Mathlib.Tactic

/-! # P0-fix: paper-faithful Theta hull over nonzero labels

| field | value |
|---|---|---|
| Status | PARTIAL: paperFaithfulThetaImage equality to the scaled region F(c_root)O is proved; the paper-faithful closure is defined and related to the scaled region; P4 positivity/finiteness of the paper hull is not yet proved (GAP). |
| Source | PaperNonzeroLabel/paperRootThetaImageNZ S793:44/79; thetaTensorScaledRegion ThetaTensorScaledImageActual:55-60; qVFamPaperThetaTensorCoefficient QVFamRootFactorCorrectionActual:61; rootHalfCoefficient RootNormalizedContainmentActual:57. |
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperFaithfulHullActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.RootHullMeasureActual
open LeanFormal.IUT.XiFPaper.Ind3OutputHullQPilotActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open MeasureTheory
open scoped Pointwise

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Monotonicity of a scaled region in the exponent vector (F is antitone). -/
theorem thetaTensorScaledRegion_mono {a c : qVFamTensorV → Real}
    (h : ∀ i, a i ≤ c i) :
    thetaTensorScaledRegion (places := qVFamTensorPlaces T b)
      (tuple := qVFamTensorTuple) c ⊆
      thetaTensorScaledRegion (places := qVFamTensorPlaces T b)
        (tuple := qVFamTensorTuple) a := by
  intro x hx
  unfold thetaTensorScaledRegion at hx ⊢
  have hF : arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
      qVFamTensorTuple c ≤ arithmeticTupleFractionalLattice
      (qVFamTensorPlaces T b) qVFamTensorTuple a :=
    arithmeticTupleFractionalLattice_mono (places := qVFamTensorPlaces T b)
      (tuple := qVFamTensorTuple) h
  exact (Submodule.mul_le.mpr fun u hu v hv =>
    Submodule.mul_mem_mul (hF hu) hv) hx

/-- Finitary paper-faithful image: union over PaperNonzeroLabel (j != 0). -/
noncomputable def paperFaithfulThetaImage : Set (qVFamTensorBlock T b) :=
  ⋃ j : PaperNonzeroLabel (l := l),
    thetaTensorScaledRegion (places := qVFamTensorPlaces T b)
      (tuple := qVFamTensorTuple)
      (fun _ => qVFamPaperThetaTensorCoefficient T b j.1)

/-- The finitary nonzero image equals the single scaled region at c_root. -/
theorem paperFaithfulThetaImage_eq_scaledRegion :
    paperFaithfulThetaImage (l := l) T b =
      thetaTensorScaledRegion (places := qVFamTensorPlaces T b)
        (tuple := qVFamTensorTuple) (fun _ => qVFamPaperRootCoefficient T b) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
    apply thetaTensorScaledRegion_mono (T := T) (b := b)
      (a := fun _ => qVFamPaperRootCoefficient T b)
      (c := fun _ => qVFamPaperThetaTensorCoefficient T b j.1)
    · intro i
      have hj1 : (1 : Real) ≤ ((gaussExponent j.1.1).toNat : Real) :=
        by exact_mod_cast one_le_gaussExponent_of_ne_zero (l := l) j.2
      have hc : 0 ≤ qVFamPaperRootCoefficient T b := by
        unfold qVFamPaperRootCoefficient
        positivity
      unfold qVFamPaperThetaTensorCoefficient
      nlinarith
    · exact hj
  · intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨oneLabel l, paperOneLabel_ne_zero (l := l)⟩, ?_⟩
    simpa [qVFamPaperThetaTensorCoefficient, gaussExponent_oneLabel] using hx

/-- Paper-faithful closure hull. -/
noncomputable def paperFaithfulThetaHull : Set (qVFamTensorBlock T b) :=
  closure (paperFaithfulThetaImage (l := l) T b)

/-- The closure is the closure of the single scaled region. -/
theorem paperFaithfulThetaHull_eq_closure_scaledRegion :
    paperFaithfulThetaHull (l := l) T b =
      closure (thetaTensorScaledRegion (places := qVFamTensorPlaces T b)
        (tuple := qVFamTensorTuple) (fun _ => qVFamPaperRootCoefficient T b)) := by
  unfold paperFaithfulThetaHull
  rw [paperFaithfulThetaImage_eq_scaledRegion]

/-- Existing green P4 datum for the Ind3 output hull. -/
theorem ind3OutputHull_measure_pos_lt_top
    [MeasurableSpace (qVFamTensorBlock T b)]
    [BorelSpace (qVFamTensorBlock T b)]
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] :
    0 < mu (ind3OutputHull (l := l) T b) ∧
      mu (ind3OutputHull (l := l) T b) < ⊤ :=
  ⟨rootNormHull_measure_pos (l := l) T b mu,
    ind3OutputHull_measure_lt_top (l := l) T b mu⟩

def rows : List (String × String × String) :=
  [ ("paperFaithfulThetaImage_eq_scaledRegion", "union over PaperNonzeroLabel = F(cRoot)O", "PROVED"),
    ("paperFaithfulThetaHull_eq_closure_scaledRegion", "hull = closure(F(cRoot)O)", "PROVED"),
    ("ind3OutputHull_measure_pos_lt_top", "P4 Ind3 hull positive finite", "PROVED (existing)"),
    ("paperFaithful P4", "positive/finite for paper hull", "GAP (not proved in this pass)") ]

theorem rows_length : rows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1PaperFaithfulHullActual

end
