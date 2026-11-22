import tmp.sheaf.xif.paper.S1187NonReflKummerCommonGroupActual
import tmp.sheaf.xif.paper.S1188NonReflKummerLayerActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows

/-! # S1195: actual evaluation arrow from the non-refl common-group layer -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1195ActualUpperEnv

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1187NonReflKummerCommonGroupActual
open LeanFormal.IUT.XiFPaper.S1188NonReflKummerLayerActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

abbrev S10 : FPrimeStrip.{umon, uv, upi} V := I.fPrimeStripAt 1 0
abbrev S11 : FPrimeStrip.{umon, uv, upi} V := I.fPrimeStripAt 1 1

local instance topS10 : ∀ v : V, TopologicalSpace ((S10 (I := I)).Pi v) :=
  fun _ => ⊥

abbrev GG : Type _ := GraphGroup (upper := S10 (I := I))

noncomputable def upperEnvLayer :
    SourceTimesMuKummerLayer (GG (I := I)) (S10 (I := I)) (S11 (I := I)) :=
  S1188NonReflKummerLayerActual.nonreflKummerLayer (upper := S10 (I := I)) (lower := S11 (I := I))
    (I.fLinkAt 1 0 1 1)

noncomputable def upperEnvUnit :
    SourceEvaluationUnitPortion (GG (I := I)) (S10 (I := I)) (S11 (I := I)) :=
  SourceEvaluationUnitPortion.ofKummerLayer (upperEnvLayer (I := I))

noncomputable def upperEnv :
    SourceEvaluationArrow (GG (I := I)) (S10 (I := I)) (S11 (I := I)) :=
  sourceEvaluationArrowOfUnitPortion
    (G := GG (I := I)) (I.fLinkAt 1 0 1 1) (upperEnvUnit (I := I))

theorem upperEnv_stripIso :
    (upperEnv (I := I)).stripIso = I.fLinkAt 1 0 1 1 := rfl

theorem upperEnv_unitPortion :
    (upperEnv (I := I)).unitPortion = upperEnvUnit (I := I) := rfl

end LeanFormal.IUT.XiFPaper.S1195ActualUpperEnv

end