import tmp.sheaf.xif.paper.Mzk1Cor312FinalSelfChecksActual
import tmp.sheaf.xif.paper.Mzk1Cor312FinalStatementActual
import tmp.sheaf.xif.paper.Mzk1KummerRealizationActual
import tmp.sheaf.xif.paper.Mzk1Cor312SignedMagnitudeChecksActual

/-!
# A559 resolved acceptance bundle for Cor 3.12

Chain state: `Mzk1Cor312FinalAssemblyActual` / `FinalStatementActual` /
`FinalSelfChecksActual` green; `paperKummerReading_strict` gives the genuine
strict volume increase; axiom gate shows only `propext`, `Classical.choice`,
`Quot.sound`.

This file packages the resolved acceptance facts (no `True`, no `sorry`):
* signed paper inequality `qReading <= thetaReading` (IUT III 10324-10353);
* strict version `qReading < thetaReading` (non-vacuity);
* `C_Theta >= -1` form;
* signed/magnitude equivalence.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptedFinalActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312SignedMagnitudeChecksActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The signed paper inequality: `-|log q| <= -|log Theta|`. -/
theorem accepted_signed_inequality (R : PaperKummerReading T) :
    R.qReading ≤ R.thetaReading :=
  paperKummerReading_le T R

/-- Strict reading comparison (non-vacuity). -/
theorem accepted_strict (R : PaperKummerReading T) :
    R.qReading < R.thetaReading :=
  paperKummerReading_strict T R

/-- `C_Theta >= -1` form of the paper statement. -/
theorem accepted_CTheta (R : PaperKummerReading T) (hqneg : R.qReading < 0)
    {C : Real} (hC : R.thetaReading ≤ C * (-R.qReading)) :
    -1 ≤ C := by
  have hqpos : 0 < -R.qReading := neg_pos.mpr hqneg
  have h1 : R.qReading < C * (-R.qReading) :=
    lt_of_lt_of_le (paperKummerReading_strict T R) hC
  have h2 : R.qReading / (-R.qReading) < C := (div_lt_iff₀ hqpos).mpr h1
  have h3 : R.qReading / (-R.qReading) = -1 := by
    have hne : R.qReading ≠ 0 := by
      intro hzero
      have h := paperKummerReading_strict T R
      rw [hzero] at h
      linarith
    rw [div_neg, div_self hne]
  rw [h3] at h2
  linarith

/-- Signed/magnitude equivalence for the paper forms. -/
theorem accepted_magnitude_iff {qMag thetaMag : Real} :
    -thetaMag ≤ -qMag ↔ qMag ≤ thetaMag :=
  signed_ineq_iff_magnitude'

end LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptedFinalActual
