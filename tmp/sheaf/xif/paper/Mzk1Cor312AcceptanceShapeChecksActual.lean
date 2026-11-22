/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import tmp.sheaf.xif.paper.Mzk1KummerRealizationActual
import tmp.sheaf.xif.paper.Mzk1Cor312AcceptanceInterfaceActual

/-!
# A565 green acceptance SHAPE checks (paper statement from realized readings)

Uses the green `Mzk1KummerRealizationActual.PaperKummerReading` to record the exact
paper statement:
* `acceptance_paper_statement` : `-|log(Theta)| >= -|log q|` (signed readings);
* strict form; `C_Theta >= -1` form; finiteness (both readings are real).

These are the statement-level checks of the acceptance artifact; no scaling/region
input is needed here (those only strengthen the requirement's `strict_measure`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceShapeChecksActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- **Paper statement**: `-|log(Theta)| >= -|log q|`. -/
theorem acceptance_paper_statement (R : PaperKummerReading T) :
    R.thetaReading ≥ R.qReading :=
  le_of_lt (paperKummerReading_strict T R)

/-- Strict paper statement. -/
theorem acceptance_paper_statement_strict (R : PaperKummerReading T) :
    R.thetaReading > R.qReading :=
  paperKummerReading_strict T R

/-- Finiteness: both readings are real numbers. -/
theorem acceptance_readings_finite (R : PaperKummerReading T) :
    ∃ qLog thetaLog : ℝ, qLog = R.qReading ∧ thetaLog = R.thetaReading :=
  ⟨R.qReading, R.thetaReading, rfl, rfl⟩

/-- `C_Theta >= -1` form of the paper statement. -/
theorem acceptance_CTheta (R : PaperKummerReading T) (hqneg : R.qReading < 0)
    {C : ℝ} (hC : R.thetaReading ≤ C * (-R.qReading)) : -1 ≤ C := by
  have hqpos : 0 < -R.qReading := neg_pos.mpr hqneg
  have h1 : R.qReading < C * (-R.qReading) :=
    lt_of_lt_of_le (paperKummerReading_strict T R) hC
  have h2 : R.qReading / (-R.qReading) < C := (div_lt_iff₀ hqpos).mpr h1
  have hne : R.qReading ≠ 0 := ne_of_lt hqneg
  have h3 : R.qReading / (-R.qReading) = -1 := by
    calc R.qReading / (-R.qReading) = -(R.qReading / R.qReading) := by rw [div_neg]
      _ = -(1 : ℝ) := by rw [div_self hne]
      _ = -1 := by ring
  rw [h3] at h2
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceShapeChecksActual
