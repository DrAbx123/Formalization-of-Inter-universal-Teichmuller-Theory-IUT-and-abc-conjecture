/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0LNormReadoutActual
import tmp.sheaf.xif.paper.Mzk1P0LNormReadoutProductActual
import tmp.sheaf.xif.paper.Mzk1P0LNormComparisonConditionalActual
import tmp.sheaf.xif.paper.BadPlacePaperNormalizedComparisonActual
import tmp.sheaf.xif.paper.Mzk1P1NormalizedSourceConditionalActual
import tmp.sheaf.xif.paper.Mzk1P1PaperSumsToS3137BridgeActual
import tmp.sheaf.xif.paper.Mzk1P1PaperSumsA1DataActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.Mzk1RouteAFinalNoS45WrapperActual
import tmp.sheaf.xif.paper.Mzk1P0QVFamNormBridgeDonorActual
import Mathlib.Tactic

/-! # P0/P1: final S3137 conditional targets (paper side + L side)

Paper side: S45SourceFields gives the paper-normalized comparison.
L side: explicit readout lock + bound + log(unitMass) >= 0 give LPaperInstance.
No unitMass=1; no True placeholder; A1Data is constructed (unconditional, see
Mzk1P1PaperSumsA1DataActual). -/

noncomputable section
open scoped BigOperators ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1P0FinalS3137ConditionalActual

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
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedComparisonActual
open LeanFormal.IUT.XiFPaper.Mzk1P1NormalizedSourceConditionalActual
open LeanFormal.IUT.XiFPaper.Mzk1P1PaperSumsToS3137BridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1P1PaperSumsA1DataActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteAFinalNoS45WrapperActual
open LeanFormal.IUT.XiFPaper.Mzk1P0QVFamNormBridgeDonorActual
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

theorem finalPaperNormalizedComparison_strict
    (S : S45SourceFields (T := T)) :
    paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T := by
  rcases S with ⟨Sfields⟩
  exact paperNormalizedComparison_of_sourceFields T Sfields

/-- **S45-free paper comparison, conditional on the pointwise normalized-vs-default
power bridge.**  Once the bridge is unconditional, this becomes the final s45-free
comparison (the correction is nonpositive by Route A). -/
theorem finalPaperNormalizedComparison_noS45_ofNormBridge
    (hbridge : ∀ b : Bad (nativePlaceSelection T),
      qVFamNormalizedNorm T b =
        (qVFamDefaultNorm T b) ^
          (1 / (relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b) : ℝ))) :
    paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T :=
  LeanFormal.IUT.XiFPaper.Mzk1RouteAFinalNoS45WrapperActual.finalPaperNormalizedComparison_noS45_of_norm_bridge T
    (fun b => relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b))
    (fun b => Nat.succ_le_of_lt (relativeCompletionDegree_pos (k := ℚ) (qVFamTensorPlace T b)))
    (fun b => by simpa using hbridge b)

/-- **S45-free final paper comparison (unconditional).**  Route A: the correction is
nonpositive because the normalized norm dominates the default norm; no
`qVFamNormRatio = 1` equality is needed. -/
theorem finalPaperNormalizedComparison :
    paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T :=
  Mzk1P0QVFamNormBridgeDonorActual.finalPaperNormalizedComparison_noS45 (T := T)

theorem finalLPaperInstance
    (hlock : thetaNormReadL (I := I) (place := place) = thetaNormReadProduct T)
    (hbound : qReadActual I place ≤ thetaNormReadProduct T)
    (hlog : 0 ≤ Real.log (actualUnitMassL (I := I) (place := place))) :
    LPaperInstance I place :=
  LPaperInstance_of_bounds (I := I) (place := place) (T := T) hlock hbound hlog

structure FinalBridgeConditions where
  s45 : S45SourceFields (T := T)
  relFactor : RelativeFactorTowerData (T := T)
  a1 : PaperToS3137A1Data (T := T)

theorem finalBridgeConditions_of
    (s45 : S45SourceFields (T := T))
    (rel : RelativeFactorTowerData (T := T)) :
    FinalBridgeConditions (T := T) := by
  letI := hM
  letI := hB
  exact { s45 := s45, relFactor := rel, a1 := paperToS3137A1Data (T := T) }

def finalBridgeConditionRows : List (String × String × String) :=
  [ ("finalPaperNormalizedComparison", "S45-free paper normalized comparison (Route A: correction <= 0; from donor noS45)", "PROVED (unconditional, no S45)"),
    ("finalPaperNormalizedComparison_strict", "S45 => strict correction-zero comparison (kept for strict/R2)", "PROVED (conditional, strict only)"),
    ("finalLPaperInstance", "lock + bound + log unitMass >= 0 => LPaperInstance", "PROVED (conditional)"),
    ("finalBridgeConditions_of", "S45 + RelativeFactor => bridge conditions (A1Data constructed)", "PROVED"),
    ("S45SourceFields", "S45 normalized-source condition; needed only for strict equality/correction-zero", "EXPLICIT CONDITION (strict only)"),
    ("RelativeFactorTowerData", "divisibility A|C (not field tower)", "EXPLICIT CONDITION"),
    ("PaperToS3137A1Data", "constructed (unconditional, A1Data file)", "CONSTRUCTED"),
    ("PaperS3137ReadingDictionary", "CONSTRUCTED (substantive PaperS3137ObjectLock; sign/unitMass explicit)", "CONSTRUCTED (given lock)"),
    ("PaperS3137ObjectLock", "explicit substantive equality data: B_b/B_pos, d_b = B_b*[K_w:F_v], unitMass_eq, theta signed equation", "EXPLICIT SUBSTANTIVE CONDITION"),
    ("unitMass = 1", "not assumed", "NOT CLAIMED"),
    ("old raw S3137 P", "vacuous", "RECORD ONLY") ]

theorem finalBridgeConditionRows_length : finalBridgeConditionRows.length = 11 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P0FinalS3137ConditionalActual

end