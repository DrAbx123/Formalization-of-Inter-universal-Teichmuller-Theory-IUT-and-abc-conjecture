import tmp.sheaf.xif.paper.LogKummerCorrespondenceFromSource
import tmp.sheaf.xif.paper.ThetaLinkLogKummerActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceKummerEvaluationSquareExtension

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.ThetaLinkIPLFactorizationActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.LogKummerCorrespondenceFromSource

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

abbrev S00 : FPrimeStrip V := I.fPrimeStripAt 0 0
abbrev S01 : FPrimeStrip V := I.fPrimeStripAt 0 1
abbrev S10 : FPrimeStrip V := I.fPrimeStripAt 1 0
abbrev S11 : FPrimeStrip V := I.fPrimeStripAt 1 1

abbrev G : Type _ := ActualKummerGroup (I := I)

noncomputable def actualUpperEvaluation : SourceEvaluationArrow (G I) (S00 I) (S01 I) :=
  sourceEvaluationArrowOfUnitPortion (I.fLinkAt 0 0 0 1)
    (actualEvaluationUnitOf (I := I) (S00 I) (S01 I)
      (I.fLinkAt 1 0 0 0) (I.fLinkAt 1 0 0 1))

noncomputable def actualLeftKummer : SourceKummerArrow (G I) (S10 I) (S00 I) :=
  sourceKummerArrowOfLayer
    ((I.fLinkAt 1 0 1 0).symm.trans (I.fLinkAt 1 0 0 0))
    (actualKummerLayerOf (I := I) (S10 I) (S00 I)
      (I.fLinkAt 1 0 1 0) (I.fLinkAt 1 0 0 0))

noncomputable def actualRightKummer : SourceKummerArrow (G I) (S11 I) (S01 I) :=
  sourceKummerArrowOfLayer
    ((I.fLinkAt 1 0 1 1).symm.trans (I.fLinkAt 1 0 0 1))
    (actualKummerLayerOf (I := I) (S11 I) (S01 I)
      (I.fLinkAt 1 0 1 1) (I.fLinkAt 1 0 0 1))

noncomputable def actualLowerUnit : SourceEvaluationUnitPortion (G I) (S10 I) (S11 I) :=
  actualEvaluationUnitOf (I := I) (S10 I) (S11 I)
    (I.fLinkAt 1 0 1 0) (I.fLinkAt 1 0 1 1)

noncomputable def actualLowerEvaluation : SourceEvaluationArrow (G I) (S10 I) (S11 I) :=
  sourceEvaluationArrowOfUnitPortion
    ((I.fLinkAt 1 0 1 0).symm.trans (I.fLinkAt 1 0 1 1))
    (actualLowerUnit I)

noncomputable def actualSquare :
    SourceKummerEvaluationSquare (G I) (S00 I) (S01 I) (S10 I) (S11 I) :=
  SourceKummerEvaluationSquare.ofThreeLegs (actualUpperEvaluation I) (actualLeftKummer I)
    (actualRightKummer I) (actualLowerUnit I)

theorem actualSquare_commutes :
    (actualSquare I).domainExpression = (actualSquare I).codomainExpression :=
  (actualSquare I).commutes

noncomputable def actualThetaLinkSquareData :
    ThetaLinkSquareData (G I) (S00 I) (S01 I) (S10 I) (S11 I) where
  square := actualSquare I

noncomputable def actualThetaLinkFactorizationData :
    ThetaLinkFactorizationData (G I)
      (iplIntermediateStrip (I := I)) (iplGauStrip (I := I))
      (iplEnvStrip (I := I)) (iplCoricEnvStrip (I := I))
      (iplQPilotStrip (I := I)) where
  link :=
    { lowerHorizontal₁ := (actualIPLData (I := I)).lowerHorizontal1
      lowerHorizontal₂ := (actualIPLData (I := I)).lowerHorizontal2
      kummer := (actualIPLData (I := I)).kummer
      evaluation := (actualIPLData (I := I)).evaluation
      inputLink := (actualIPLData (I := I)).inputLink
      factorization := by
        simpa [SourceLinkFactorization.composite, IPLActual.composite]
          using (actualIPLData (I := I)).factorization }

theorem actualThetaLinkFactorization_inputLink_eq_composite :
    (actualThetaLinkFactorizationData I).link.inputLink =
      (actualThetaLinkFactorizationData I).link.composite :=
  (actualThetaLinkFactorizationData I).link.inputLink_eq_composite

theorem actualThetaLinkSquareData_commutes :
    (actualThetaLinkSquareData I).square.domainExpression =
      (actualThetaLinkSquareData I).square.codomainExpression :=
  (actualThetaLinkSquareData I).square.domainExpression_eq_codomainExpression

end LeanFormal.IUT.XiFPaper.ThetaLinkIPLFactorizationActual
