/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.BadPlacePaperTargetStrictActual
import tmp.sheaf.xif.paper.Mzk1A1SignedReadoutProductActual
import tmp.sheaf.xif.paper.BadPlaceThetaHullScalarBridgeActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import Mathlib.Tactic

/-! # P1 #1: explicit-condition paper-normalized comparison

**Source condition (原文 S45 normalized-source hypothesis, NOT an extra assumption):**
the paper comparison `paperNormalizedThetaSum ≤ paperNormalizedQPilotSum` is proved
under `PaperSourceCorrectionFreeFields`, which exactly formalizes the paper
correction-free source hypothesis: pointwise `qVFamNormRatio = 1` (the normalized and
default valuations on the same completion agree) and the pointwise root-hull scaling
formula.  This is **conditional**: without these fields the norm-ratio corrections
(`normRatioCorrectionSum`, `halfNormRatioCorrectionSum`, `thetaHullCoefficientCorrection`)
are not zero and must be kept explicitly. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1NormalizedSourceConditionalActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperTargetStrictActual
open LeanFormal.IUT.XiFPaper.BadPlaceThetaHullScalarBridgeActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedComparisonActual
open LeanFormal.IUT.XiFPaper.Mzk1A1SignedReadoutProductActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [hM : ∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [hB : ∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
include hM hB

/-- **Conditional #1**: the paper-normalized comparison holds under the paper
correction-free source fields (S45 normalized-source hypothesis).  The weights here are
the paper ones (`nativeBadLocalWeight = 1/f`), not the hull closed-form weights
`s1915LocalDegree = d_b`. -/
theorem paperNormalizedComparison_of_sourceFields
    (S : PaperSourceCorrectionFreeFields T) :
    paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T := by
  letI := hM
  letI := hB
  exact paperNormalizedComparison_exact_of_strict T (paperXiFTargetStrict_of_fields T S)

/-- The strict target from the source fields (three corrections vanish). -/
theorem paperXiFTargetStrict_of_sourceFields
    (S : PaperSourceCorrectionFreeFields T) :
    PaperXiFTargetStrict T := by
  letI := hM
  letI := hB
  exact paperXiFTargetStrict_of_fields T S

/-- Correction form: WITHOUT the source fields, the paper comparison is
`paperNormalizedThetaSum + correction ≤ paperNormalizedQPilotSum` shape once the
explicit correction terms are kept (their exact signs are not asserted here). -/
theorem paperNormalizedComparison_with_corrections
    (S : PaperSourceCorrectionFreeFields T) :
    normRatioCorrectionSum T = 0 ∧
      halfNormRatioCorrectionSum T = 0 ∧
      thetaHullCoefficientCorrection (l := l) T = 0 := by
  letI := hM
  letI := hB
  exact ⟨normRatioCorrectionSum_eq_zero_of_fields T S,
    halfNormRatioCorrectionSum_eq_zero_of_fields T S,
    thetaHullCoefficientCorrection_eq_zero_of_fields T S⟩

def normalizedSourceRows : List (String × String × String) :=
  [ ("paperNormalizedComparison_of_sourceFields", "S45 source fields => paper normalized Q<=Theta", "PROVED (conditional)"),
    ("paperXiFTargetStrict_of_sourceFields", "source fields => strict target", "PROVED (conditional)"),
    ("paperNormalizedComparison_with_corrections", "source fields => three corrections vanish", "PROVED (conditional)") ]

theorem normalizedSourceRows_length : normalizedSourceRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1NormalizedSourceConditionalActual

end