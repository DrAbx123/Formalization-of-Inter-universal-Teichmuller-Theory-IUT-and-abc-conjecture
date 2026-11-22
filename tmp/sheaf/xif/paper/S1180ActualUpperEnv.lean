import tmp.sheaf.xif.paper.LogKummerCorrespondenceFromSource

/-! # S1180: actual evaluation arrow for the (1,0) -> (1,1) env edge -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.Theorem311Source.S1180ActualUpperEnv

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.FPrimeStrip
open LeanFormal.IUT.Theorem311Source.LogKummerCorrespondenceFromSource

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

abbrev G : Type _ := ActualKummerGroup (I := I)

noncomputable def upperEnvLayer :
    SourceTimesMuKummerLayer (G (I := I))
      (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 1) :=
  actualKummerLayerOf (I := I)
    (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 1)
    (FPrimeStripEquiv.refl (I.fPrimeStripAt 1 0))
    (I.fLinkAt 1 0 1 1)

noncomputable def upperEnvUnit :
    SourceEvaluationUnitPortion (G (I := I))
      (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 1) :=
  actualEvaluationUnitOf (I := I)
    (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 1)
    (FPrimeStripEquiv.refl (I.fPrimeStripAt 1 0))
    (I.fLinkAt 1 0 1 1)

noncomputable def upperEnvArrow :
    SourceEvaluationArrow (G (I := I))
      (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 1) :=
  sourceEvaluationArrowOfUnitPortion
    (G := G (I := I))
    (I.fLinkAt 1 0 1 1) (upperEnvUnit (I := I))

end LeanFormal.IUT.Theorem311Source.S1180ActualUpperEnv

end
