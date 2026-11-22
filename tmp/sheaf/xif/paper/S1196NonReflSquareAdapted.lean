import tmp.sheaf.xif.paper.S1195ActualUpperEnv
import tmp.sheaf.xif.paper.ThetaLinkIPLFactorizationActual

/-! # S1196: non-refl upperEnv in the actual Kummer/evaluation square -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1196NonReflSquareAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

abbrev S00 : FPrimeStrip.{umon, uv, upi} V :=
  ThetaLinkIPLFactorizationActual.S00 (I := I)
abbrev S01 : FPrimeStrip.{umon, uv, upi} V :=
  ThetaLinkIPLFactorizationActual.S01 (I := I)
abbrev S10 : FPrimeStrip.{umon, uv, upi} V :=
  ThetaLinkIPLFactorizationActual.S10 (I := I)
abbrev S11 : FPrimeStrip.{umon, uv, upi} V :=
  ThetaLinkIPLFactorizationActual.S11 (I := I)

local instance topS10 : ∀ v : V, TopologicalSpace ((S10 (I := I)).Pi v) :=
  fun _ => ⊥

abbrev G : Type _ := (v : V) → (S10 (I := I)).Pi v

noncomputable def nonreflUpperEnv :
    SourceEvaluationArrow (G (I := I)) (S10 (I := I)) (S11 (I := I)) :=
  S1195ActualUpperEnv.upperEnv (I := I)

noncomputable def nonreflSquare :
    SourceKummerEvaluationSquare (G (I := I))
      (S00 (I := I)) (S01 (I := I)) (S10 (I := I)) (S11 (I := I)) :=
  SourceKummerEvaluationSquare.ofThreeLegs
    (nonreflUpperEnv (I := I))
    (ThetaLinkIPLFactorizationActual.actualLeftKummer (I := I))
    (ThetaLinkIPLFactorizationActual.actualRightKummer (I := I))
    (ThetaLinkIPLFactorizationActual.actualLowerUnit (I := I))

theorem nonreflSquare_commutes :
    (nonreflSquare (I := I)).domainExpression =
      (nonreflSquare (I := I)).codomainExpression :=
  (nonreflSquare (I := I)).commutes

noncomputable def nonreflThetaLinkSquareData :
    ThetaLinkSquareData (G (I := I))
      (S00 (I := I)) (S01 (I := I)) (S10 (I := I)) (S11 (I := I)) where
  square := nonreflSquare (I := I)

end LeanFormal.IUT.XiFPaper.S1196NonReflSquareAdapted

end
