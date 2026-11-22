/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0FinalS3137ConditionalActual
import tmp.sheaf.xif.paper.Mzk1P0FinalS3137DictionaryActual
import tmp.sheaf.xif.paper.Mzk1P0QVFamNormBridgeDonorActual
import Mathlib.Tactic

/-! # Final/Dictionary drop-S assembly (prepared integration)

One pointwise normalized-vs-default norm bridge `hbridge`
(`qVFamNormalizedNorm = qVFamDefaultNorm^(1/d)`) supplies:
* the paper-normalized comparison WITHOUT the S45 equality `qVFamNormRatio = 1`;
* the combined final target `comparison ∧ RelativeFactorTowerData ∧ Nonempty Dictionary`.

Once the unconditional hbridge is available, the two theorems below are instantiated with
`hbridge := fun b => <hbridge theorem> T b` and become the S45-free final targets.
No fake: hbridge is a POWER relation; no norm equality; S45 remains strict-only. -/

noncomputable section
open scoped BigOperators ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1P0FinalNoS45AssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorLActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LNormReadoutActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LNormReadoutProductActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LNormComparisonConditionalActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedComparisonActual
open LeanFormal.IUT.XiFPaper.Mzk1P1NormalizedSourceConditionalActual
open LeanFormal.IUT.XiFPaper.Mzk1P1PaperSumsToS3137BridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1P1PaperSumsA1DataActual
open LeanFormal.IUT.XiFPaper.Mzk1P0FinalS3137ConditionalActual
open LeanFormal.IUT.XiFPaper.Mzk1P0QVFamNormBridgeDonorActual
open LeanFormal.IUT.XiFPaper.Mzk1P0FinalS3137DictionaryActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open MeasureTheory

universe ua upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [hM : ∀ b : Bad (nativePlaceSelection T),
  MeasurableSpace (qVFamTensorBlock T b)]
variable [hB : ∀ b : Bad (nativePlaceSelection T),
  BorelSpace (qVFamTensorBlock T b)]
include hM hB

/-- Pointwise normalized-vs-default power bridge (the single input for drop-S). -/
def NormPowerBridge : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    qVFamNormalizedNorm T b =
      (qVFamDefaultNorm T b) ^
        (1 / (relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b) : ℝ))

/-- **Drop-S comparison**: paper-normalized comparison with no S45 equality. -/
theorem finalPaperNormalizedComparison_noS45
    (hbridge : NormPowerBridge (T := T)) :
    paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T :=
  finalPaperNormalizedComparison_noS45_ofNormBridge (T := T) hbridge

/-- **Drop-S combined target**: comparison ∧ relative-factor data ∧ nonempty Dictionary. -/
theorem finalDictionaryCombined_noS45
    (hbridge : NormPowerBridge (T := T))
    (rel : RelativeFactorTowerData (T := T))
    (lock : PaperS3137ObjectLock I place T) :
    (paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T) ∧
      RelativeFactorTowerData (T := T) ∧
      Nonempty (PaperS3137ReadingDictionary (I := I) (place := place) (T := T)
        (hM := hM) (hB := hB) (lock := lock)) :=
  finalDictionaryCombined_ofNormBridge (I := I) (place := place) (T := T)
    (hM := hM) (hB := hB) hbridge rel lock

/-- The unconditional norm power bridge, from the hull-provided hbridge. -/
theorem normPowerBridge_holds : NormPowerBridge (T := T) :=
  fun b => qVFamNormalizedNorm_eq_defaultNorm_rpow (T := T) (b := b)

/-- **Unconditional drop-S comparison.** -/
theorem finalPaperNormalizedComparison_noS45_uncond :
    paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T :=
  finalPaperNormalizedComparison_noS45 (T := T) (normPowerBridge_holds (T := T))

/-- **Unconditional drop-S combined target.** -/
theorem finalDictionaryCombined_noS45_uncond
    (rel : RelativeFactorTowerData (T := T))
    (lock : PaperS3137ObjectLock I place T) :
    (paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T) ∧
      RelativeFactorTowerData (T := T) ∧
      Nonempty (PaperS3137ReadingDictionary (I := I) (place := place) (T := T)
        (hM := hM) (hB := hB) (lock := lock)) :=
  finalDictionaryCombined_noS45 (I := I) (place := place) (T := T)
    (hM := hM) (hB := hB) (normPowerBridge_holds (T := T)) rel lock

def noS45AssemblyRows : List (String × String × String) :=
  [ ("NormPowerBridge", "pointwise normalized = default^(1/d) power bridge", "EXPLICIT INPUT (power, not equality)"),
    ("normPowerBridge_holds", "hull hbridge provides the power bridge unconditionally", "PROVED (from hull provider)"),
    ("finalPaperNormalizedComparison_noS45_uncond", "unconditional paper comparison without S45", "PROVED (unconditional)"),
    ("finalDictionaryCombined_noS45_uncond", "unconditional comparison ∧ relativeFactor ∧ Dictionary", "PROVED (unconditional)"),
    ("finalPaperNormalizedComparison_noS45", "bridge => paper comparison without S45", "PROVED (conditional on bridge)"),
    ("finalDictionaryCombined_noS45", "bridge => comparison ∧ relativeFactor ∧ Dictionary", "PROVED (conditional on bridge)"),
    ("S45 qVFamNormRatio = 1", "only for strict equality/correction-zero; not needed for comparison", "NOT USED") ]

theorem noS45AssemblyRows_length : noS45AssemblyRows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P0FinalNoS45AssemblyActual

end