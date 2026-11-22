import tmp.sheaf.xif.paper.LogKummerCorrespondenceFromSource
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceEvaluationUnitPortionConjugation
/-! # S1180: actual upperEnv from actual fLinkAt and Kummer layer
upper = I.fPrimeStripAt 1 0, lower = I.fPrimeStripAt 1 1.
The strip link is the actual I.fLinkAt 1 0 1 1; the unit portion is the
actual Kummer layer conjugated from the core strip by actual fLinkAt 1 0 1 0
and 1 0 1 1, extracted with SourceEvaluationUnitPortion.ofKummerLayer.
No weak interface. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S1180SourceUpperEnvActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.LogKummerCorrespondenceFromSource
open LeanFormal.IUT.Theorem311Source.SourceEvaluationUnitPortion
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
/-- Actual upperEnv strip: I.fPrimeStripAt 1 0 -> I.fPrimeStripAt 1 1. -/
noncomputable def upperEnvStrip : FPrimeStrip.{umon, uv, upi} V :=
  I.fPrimeStripAt 1 1
/-- Actual Kummer layer on (1 0, 1 1) from the actual source links. -/
noncomputable def upperEnvKummerLayer :
    SourceTimesMuKummerLayer (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 1) :=
  actualKummerLayerOf (I := I)
    (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 1)
    (I.fLinkAt 1 0 1 0) (I.fLinkAt 1 0 1 1)
/-- Actual evaluation unit portion extracted from the Kummer layer. -/
noncomputable def upperEnvUnitPortion :
    SourceEvaluationUnitPortion (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 1) :=
  SourceEvaluationUnitPortion.ofKummerLayer
    (upperEnvKummerLayer (I := I))
/-- Actual upperEnv SourceEvaluationArrow. -/
noncomputable def upperEnv :
    SourceEvaluationArrow (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 1) :=
  sourceEvaluationArrowOfUnitPortion
    (I.fLinkAt 1 0 1 1)
    (upperEnvUnitPortion (I := I))
theorem upperEnv_stripIso :
    (upperEnv (I := I)).stripIso = I.fLinkAt 1 0 1 1 := rfl
theorem upperEnv_unitPortion :
    (upperEnv (I := I)).unitPortion = upperEnvUnitPortion (I := I) := rfl
end LeanFormal.IUT.XiFPaper.S1180SourceUpperEnvActual
