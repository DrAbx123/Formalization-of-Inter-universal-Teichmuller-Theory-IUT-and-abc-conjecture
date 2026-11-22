/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1RootExtensionCarrierDataActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import Mathlib.Tactic

/-! # #10: normalized root-extension unit mass, conditional on SigmaFinite -/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Metric
namespace LeanFormal.IUT.XiFPaper.Mzk1NativeNormalizedUnitMassConditionalActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1RootExtensionCarrierDataActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

noncomputable def rootUnitMass (b : Bad (nativePlaceSelection T)) : ℝ≥0∞ :=
  rootExtensionHaar T b (rootExtensionUnitBall T b)

noncomputable def normalizedRootExtensionHaar (b : Bad (nativePlaceSelection T)) :
    Measure (rootNormedExtension T b) :=
  (rootUnitMass (T := T) b)⁻¹ • rootExtensionHaar T b

theorem normalizedRootExtensionHaar_unitBall
    (b : Bad (nativePlaceSelection T)) :
    normalizedRootExtensionHaar T b (rootExtensionUnitBall T b) = 1 := by
  unfold normalizedRootExtensionHaar rootUnitMass
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt (rootExtensionUnitBall_measure_pos (T := T) (b := b)))
    (ne_of_lt (rootExtensionUnitBall_measure_lt_top (T := T) (b := b)))

noncomputable def normalizedProduct : Measure (RootExtensionProductCarrier T) :=
  Measure.pi (fun b => normalizedRootExtensionHaar T b)

theorem normalizedProduct_unitBall
    [∀ b, SigmaFinite (normalizedRootExtensionHaar T b)] :
    normalizedProduct T (rootExtensionProductUnitBall T) = 1 := by
  unfold normalizedProduct rootExtensionProductUnitBall
  rw [Measure.pi_pi]
  simp [normalizedRootExtensionHaar_unitBall]

theorem normalizedUnitMass_eq_one
    [∀ b, SigmaFinite (normalizedRootExtensionHaar T b)] :
    (normalizedProduct T (rootExtensionProductUnitBall T)).toReal = 1 := by
  rw [normalizedProduct_unitBall]
  norm_num

def normalizedConditionalRows : List (String × String) :=
  [ ("normalizedRootExtensionHaar", "local unit-ball normalized to 1"),
    ("normalizedProduct_unitBall", "conditional on SigmaFinite normalized local measures"),
    ("normalizedUnitMass_eq_one", "conditional normalized unitMass=1"),
    ("SigmaFinite provider", "GAP: need instance for c⁻¹ • rootExtensionHaar") ]
theorem normalizedConditionalRows_length : normalizedConditionalRows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1NativeNormalizedUnitMassConditionalActual
