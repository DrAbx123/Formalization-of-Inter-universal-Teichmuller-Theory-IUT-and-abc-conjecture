import tmp.sheaf.xif.paper.S1195ActualUpperEnv
import tmp.sheaf.xif.paper.ThetaLinkIPLFactorizationActual
/-! # S1200 A: adjacent Kummer square with the same G/topology
upperHorizontal = S1195 nonrefl upperEnv (S10 -> S11);
left/right Kummer and lower unit are actual Kummer layers on the same
GraphGroup S10, via LogKummerCorrespondenceFromSource.actualKummerLayerOf.
Square vertices: lowerLeft=S00, lowerRight=S01, upperLeft=S10, upperRight=S11. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S1200NonReflKummerSquareActualAdapted
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.LogKummerCorrespondenceFromSource
open LeanFormal.IUT.XiFPaper.S1187NonReflKummerCommonGroupActual
open LeanFormal.IUT.XiFPaper.S1195ActualUpperEnv
open LeanFormal.IUT.XiFPaper.ThetaLinkIPLFactorizationActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
abbrev S00 : FPrimeStrip.{umon, uv, upi} V := I.fPrimeStripAt 0 0
abbrev S01 : FPrimeStrip.{umon, uv, upi} V := I.fPrimeStripAt 0 1
abbrev S10 : FPrimeStrip.{umon, uv, upi} V := I.fPrimeStripAt 1 0
abbrev S11 : FPrimeStrip.{umon, uv, upi} V := I.fPrimeStripAt 1 1
local instance topS10 : ∀ v : V, TopologicalSpace ((S10 (I := I)).Pi v) := fun _ => ⊥
abbrev G : Type _ := GraphGroup (upper := S10 (I := I))
noncomputable def upperHorizontal :
    @SourceEvaluationArrow V (G (I := I)) Pi.group Pi.topologicalSpace
      (S10 (I := I)) (S11 (I := I)) :=
  S1195ActualUpperEnv.upperEnv (I := I)
noncomputable def leftKummerLayer :
    SourceTimesMuKummerLayer (G (I := I)) (S00 (I := I)) (S10 (I := I)) :=
  actualKummerLayerOf (I := I) (S00 (I := I)) (S10 (I := I))
    (I.fLinkAt 1 0 0 0) (FPrimeStripEquiv.refl (S10 (I := I)))
noncomputable def leftKummer :
    SourceKummerArrow (G (I := I)) (S00 (I := I)) (S10 (I := I)) :=
  sourceKummerArrowOfLayer (I.fLinkAt 0 0 1 0) (leftKummerLayer (I := I))
noncomputable def rightKummerLayer :
    SourceTimesMuKummerLayer (G (I := I)) (S01 (I := I)) (S11 (I := I)) :=
  actualKummerLayerOf (I := I) (S01 (I := I)) (S11 (I := I))
    (I.fLinkAt 1 0 0 1) (I.fLinkAt 1 0 1 1)
noncomputable def rightKummer :
    SourceKummerArrow (G (I := I)) (S01 (I := I)) (S11 (I := I)) :=
  sourceKummerArrowOfLayer (I.fLinkAt 0 1 1 1) (rightKummerLayer (I := I))
noncomputable def lowerUnitLayer :
    SourceTimesMuKummerLayer (G (I := I)) (S00 (I := I)) (S01 (I := I)) :=
  actualKummerLayerOf (I := I) (S00 (I := I)) (S01 (I := I))
    (I.fLinkAt 1 0 0 0) (I.fLinkAt 1 0 0 1)
noncomputable def lowerUnit :
    SourceEvaluationUnitPortion (G (I := I)) (S00 (I := I)) (S01 (I := I)) :=
  SourceEvaluationUnitPortion.ofKummerLayer (lowerUnitLayer (I := I))
noncomputable def nonreflSquare :
    @SourceKummerEvaluationSquare V (G (I := I)) Pi.group Pi.topologicalSpace
      (S10 (I := I)) (S11 (I := I)) (S00 (I := I)) (S01 (I := I)) :=
  @SourceKummerEvaluationSquare.ofThreeLegs V (G (I := I)) Pi.group Pi.topologicalSpace
    (S10 (I := I)) (S11 (I := I)) (S00 (I := I)) (S01 (I := I))
    (upperHorizontal (I := I)) (leftKummer (I := I))
    (rightKummer (I := I)) (lowerUnit (I := I))
theorem nonreflSquare_commutes :
    (nonreflSquare (I := I)).domainExpression =
      (nonreflSquare (I := I)).codomainExpression :=
  (nonreflSquare (I := I)).commutes
end LeanFormal.IUT.XiFPaper.S1200NonReflKummerSquareActualAdapted
