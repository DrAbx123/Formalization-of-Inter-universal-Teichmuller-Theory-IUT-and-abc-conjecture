import tmp.sheaf.xif.paper.PaperThetaLinkDataActual
import tmp.sheaf.xif.paper.IPLAPTActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows

/-! # Nontrivial actual paper Theta-link strips

This file uses the actual source strips

  S n m := I.primeStripAt n m

at distinct log-theta-lattice indices and the actual Hodge-theater links

  I.linkAt n m n' m'

to build a non-diagonal strip configuration:

  intermediate = S 1 0
  gau          = S 1 0
  env          = S 0 0
  coricEnv     = S 0 1
  qPilot       = S 1 1
  upperLeft    = S 0 0
  upperRight   = S 0 1
  lowerLeft    = S 1 0
  lowerRight   = S 1 1

The strip equivalences lowerHorizontal2 and inputLink are actual source links.
The Kummer/evaluation arrows between the distinct strips are NOT supplied by
the source record: their layer/action data are explicit fields of the packet.
The IPL factorization equality and the Kummer-evaluation square are also
explicit fields.  No toy action or arbitrary arrow is fabricated.

No True/PUnit/axiom/sorry. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper
namespace PaperThetaLinkNontrivial

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper

universe ua uv upi umon ui uG

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The actual distinct source strips used by the nontrivial Theta-link. -/
abbrev intermediateStrip : FPrimeStrip V := I.primeStripAt 1 0

abbrev gauStrip : FPrimeStrip V := I.primeStripAt 1 0

abbrev envStrip : FPrimeStrip V := I.primeStripAt 0 0

abbrev coricEnvStrip : FPrimeStrip V := I.primeStripAt 0 1

abbrev qPilotStrip : FPrimeStrip V := I.primeStripAt 1 1

abbrev upperLeftStrip : FPrimeStrip V := I.primeStripAt 0 0

abbrev upperRightStrip : FPrimeStrip V := I.primeStripAt 0 1

abbrev lowerLeftStrip : FPrimeStrip V := I.primeStripAt 1 0

abbrev lowerRightStrip : FPrimeStrip V := I.primeStripAt 1 1

/-- The actual lower horizontal strip equivalence env -> gau. -/
def lowerHorizontal2Actual : FPrimeStripEquiv
    (envStrip (I := I)) (gauStrip (I := I)) :=
  (I.linkAt 0 0 1 0).primeStripEquiv

/-- The actual input strip equivalence intermediate -> qPilot. -/
def inputLinkActual : FPrimeStripEquiv
    (intermediateStrip (I := I)) (qPilotStrip (I := I)) :=
  (I.linkAt 1 0 1 1).primeStripEquiv

/-- The missing nontrivial Kummer/evaluation arrow data and factorization
equalities for the distinct strips.  These are explicit source fields. -/
structure NontrivialThetaLinkActual where
  kummer : SourceKummerArrow G
    (envStrip (I := I)) (coricEnvStrip (I := I))
  evaluation : SourceEvaluationArrow G
    (coricEnvStrip (I := I)) (qPilotStrip (I := I))
  ipl_factorization :
    inputLinkActual (I := I) =
      (FPrimeStripEquiv.refl (gauStrip (I := I))).symm.trans
        ((lowerHorizontal2Actual (I := I)).symm.trans
          (kummer.stripIso.trans evaluation.stripIso))
  kummerEvaluation : KummerEvaluationActual (G := G)
    (upperLeftStrip (I := I)) (upperRightStrip (I := I))
    (lowerLeftStrip (I := I)) (lowerRightStrip (I := I))

namespace NontrivialThetaLinkActual

variable (P : NontrivialThetaLinkActual (I := I) (G := G))

/-- Assemble the actual paper Theta-link data from the nontrivial strip packet. -/
def toPaperThetaLinkData :
    PaperThetaLinkData (G := G)
      (intermediateStrip (I := I)) (gauStrip (I := I))
      (envStrip (I := I)) (coricEnvStrip (I := I))
      (qPilotStrip (I := I)) (upperLeftStrip (I := I))
      (upperRightStrip (I := I)) (lowerLeftStrip (I := I))
      (lowerRightStrip (I := I)) where
  ipl :=
    { lowerHorizontal1 := FPrimeStripEquiv.refl (gauStrip (I := I))
      lowerHorizontal2 := lowerHorizontal2Actual (I := I)
      kummer := P.kummer
      evaluation := P.evaluation
      inputLink := inputLinkActual (I := I)
      factorization := P.ipl_factorization }
  kummerEvaluation := P.kummerEvaluation

/-- The constructed input link is the actual source link S(1,0) -> S(1,1). -/
@[simp] theorem toPaperThetaLinkData_inputLink :
    P.toPaperThetaLinkData.inputLink = inputLinkActual (I := I) := rfl

/-- The constructed Kummer evaluation is the supplied actual square. -/
@[simp] theorem toPaperThetaLinkData_kummerEvaluation :
    P.toPaperThetaLinkData.kummerEvaluation = P.kummerEvaluation := rfl

/-- The IPL factorization is the supplied factorization equality. -/
theorem toPaperThetaLinkData_ipl_factorization :
    P.toPaperThetaLinkData.ipl.inputLink =
      P.toPaperThetaLinkData.ipl.composite :=
  P.toPaperThetaLinkData.ipl_factorization

/-- The Kummer-evaluation two-path equality carried by the actual square. -/
theorem toPaperThetaLinkData_kummerEvaluation_commutes :
    P.toPaperThetaLinkData.kummerEvaluation.square.domainExpression =
      P.toPaperThetaLinkData.kummerEvaluation.square.codomainExpression :=
  P.toPaperThetaLinkData.kummerEvaluation.domainExpression_eq_codomainExpression

/-- The actual lower strip equivalence is nontrivial source data from linkAt. -/
theorem lowerHorizontal2Actual_eq :
    lowerHorizontal2Actual (I := I) =
      (I.linkAt 0 0 1 0).primeStripEquiv := rfl

/-- The actual input strip equivalence is nontrivial source data from linkAt. -/
theorem inputLinkActual_eq :
    inputLinkActual (I := I) =
      (I.linkAt 1 0 1 1).primeStripEquiv := rfl

end NontrivialThetaLinkActual

/-! ## Exact missing strip/arrow fields

The actual strips and the two Hodge-theater strip links are constructed.  The
following are not supplied by the frozen source and remain explicit fields:

1. kummer : SourceKummerArrow G (S 0 0) (S 0 1), including its
   SourceTimesMuKummerLayer and actual units action;
2. evaluation : SourceEvaluationArrow G (S 0 1) (S 1 1), including its
   SourceEvaluationUnitPortion;
3. ipl_factorization : the equality of the actual input link with the IPL
   composite for the distinct strips;
4. kummerEvaluation : KummerEvaluationActual G (S 0 0) (S 0 1) (S 1 0) (S 1 1),
   including its SourceKummerEvaluationSquare.

No trivial/identity layer is inserted and no arbitrary equivalence is chosen.
No unconditional PaperThetaLinkData with distinct strips is asserted. -/

end PaperThetaLinkNontrivial
end XiFPaper
end LeanFormal.IUT

end