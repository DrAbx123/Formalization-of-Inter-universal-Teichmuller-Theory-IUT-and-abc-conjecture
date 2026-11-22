import tmp.sheaf.xif.paper.PaperThetaLinkNontrivial
import tmp.sheaf.xif.paper.IPLAPTActual

/-!
# Nontrivial Kummer-evaluation and IPL data from actual strips

This file uses the actual distinct strips of
PaperThetaLinkNontrivial:

  S00 = I.primeStripAt 0 0
  S01 = I.primeStripAt 0 1
  S10 = I.primeStripAt 1 0
  S11 = I.primeStripAt 1 1

and the production constructors:

  SourceKummerEvaluationSquare.ofThreeLegs
  sourceKummerArrowOfLayer
  sourceEvaluationArrowOfUnitPortion

The actual source links supply the lower second horizontal
S00 -> S10 (lowerHorizontal2Actual) and the input strip link S10 -> S11
(inputLinkActual).  The four corner arrows themselves are not supplied by the
frozen source; the file therefore constructs the exact conditional data
package and feeds it through the production square/IPL constructors.  No
identity/trivial Kummer or evaluation arrow is substituted for a distinct-strip
arrow.

No True/PUnit/axiom/sorry is used.  Compilation is queued; this file is
write-only.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.NontrivialKummerEvaluationActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.PaperThetaLinkNontrivial

universe ua uv upi umon ui uG

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]

/-! ## 1. Actual four-corner strips -/

abbrev S00 : FPrimeStrip V := upperLeftStrip (I := I)

abbrev S01 : FPrimeStrip V := upperRightStrip (I := I)

abbrev S10 : FPrimeStrip V := lowerLeftStrip (I := I)

abbrev S11 : FPrimeStrip V := lowerRightStrip (I := I)

/-- The actual lower horizontal S00 -> S10 from the source Hodge-theater link. -/
def lowerHorizontalS00S10 : FPrimeStripEquiv S00 S10 :=
  lowerHorizontal2Actual (I := I)

/-- The actual input strip link S10 -> S11. -/
def inputLinkS10S11 : FPrimeStripEquiv S10 S11 :=
  inputLinkActual (I := I)

/-! ## 2. Exact missing corner arrows for the Kummer-evaluation square -/

/-- The four exact source arrows needed by the production three-legs square.
They are data, not True/PUnit slots.  The lower horizontal is forced by
ofThreeLegs from these arrows. -/
structure NontrivialKummerSquareSource where
  upperEvaluation : SourceEvaluationArrow G S00 S01
  leftKummer : SourceKummerArrow G S10 S00
  rightKummer : SourceKummerArrow G S11 S01
  lowerUnitPortion : SourceEvaluationUnitPortion G S10 S11

/-- The production three-legs construction of the nontrivial square. -/
def nontrivialSquare (D : NontrivialKummerSquareSource (I := I) (G := G)) :
    SourceKummerEvaluationSquare G S00 S01 S10 S11 :=
  SourceKummerEvaluationSquare.ofThreeLegs
    D.upperEvaluation D.leftKummer D.rightKummer D.lowerUnitPortion

/-- The actual KummerEvaluationActual at the four distinct strips. -/
def nontrivialKummerEvaluation (D : NontrivialKummerSquareSource (I := I) (G := G)) :
    KummerEvaluationActual (G := G) S00 S01 S10 S11 where
  square := nontrivialSquare (I := I) (G := G) D

/-- The two-path equality is the actual square equality, not a re-asserted
triviality. -/
theorem nontrivialKummerEvaluation_twoPath
    (D : NontrivialKummerSquareSource (I := I) (G := G)) :
    (nontrivialKummerEvaluation (I := I) (G := G) D).square.domainExpression =
      (nontrivialKummerEvaluation (I := I) (G := G) D).square.codomainExpression :=
  (nontrivialKummerEvaluation (I := I) (G := G) D).domainExpression_eq_codomainExpression

/-- The forced lower horizontal of the constructed square. -/
theorem nontrivialSquare_lowerHorizontal_stripIso
    (D : NontrivialKummerSquareSource (I := I) (G := G)) :
    (nontrivialSquare (I := I) (G := G) D).lowerHorizontal.stripIso =
      D.leftKummer.stripIso.trans
        (D.upperEvaluation.stripIso.trans D.rightKummer.stripIso.symm) :=
  SourceKummerEvaluationSquare.lowerHorizontal_stripIso_eq
    (nontrivialSquare (I := I) (G := G) D)

/-! ## 3. Exact missing arrows for the IPL factorization -/

/-- The two exact source arrows for the nontrivial IPL composite.  The lower
horizontal links are actual source links; the Kummer/evaluation arrows between
distinct strips are the missing source fields. -/
structure NontrivialIPLSource where
  kummer : SourceKummerArrow G S00 S01
  evaluation : SourceEvaluationArrow G S01 S11

/-- The IPL composite expression for the actual distinct strips. -/
def iplComposite (P : NontrivialIPLSource (I := I) (G := G)) :
    FPrimeStripEquiv S10 S11 :=
  (FPrimeStripEquiv.refl S10).symm.trans
    ((lowerHorizontalS00S10 (I := I)).symm.trans
      (P.kummer.stripIso.trans P.evaluation.stripIso))

/-- The nontrivial IPLActual, with inputLink set to the composite.  The
factorization field is therefore definitional, while the composite itself
contains the actual lower source link and the two missing distinct-strip
arrows. -/
def nontrivialIpl (P : NontrivialIPLSource (I := I) (G := G)) :
    IPLActual (G := G) S10 S10 S00 S01 S11 where
  lowerHorizontal1 := FPrimeStripEquiv.refl S10
  lowerHorizontal2 := lowerHorizontalS00S10 (I := I)
  kummer := P.kummer
  evaluation := P.evaluation
  inputLink := iplComposite (I := I) (G := G) P
  factorization := rfl

/-- The nontrivial IPL factorization equality. -/
theorem nontrivialIpl_factorization
    (P : NontrivialIPLSource (I := I) (G := G)) :
    (nontrivialIpl (I := I) (G := G) P).inputLink =
      (nontrivialIpl (I := I) (G := G) P).composite :=
  (nontrivialIpl (I := I) (G := G) P).inputLink_eq_composite

/-- The IPL input link is the composite built from the actual lower link and
the supplied Kummer/evaluation arrows. -/
@[simp] theorem nontrivialIpl_inputLink
    (P : NontrivialIPLSource (I := I) (G := G)) :
    (nontrivialIpl (I := I) (G := G) P).inputLink =
      iplComposite (I := I) (G := G) P :=
  rfl

/-! ## 4. The combined nontrivial packet -/

/-- All exact source fields needed for both constructions.  This is a named
data package, not an asserted inhabitant. -/
structure NontrivialKummerIPLSource where
  square : NontrivialKummerSquareSource (I := I) (G := G)
  ipl : NontrivialIPLSource (I := I) (G := G)

/-- The actual KummerEvaluationActual from the combined packet. -/
def nontrivialKummerEvaluationOfPacket
    (D : NontrivialKummerIPLSource (I := I) (G := G)) :
    KummerEvaluationActual (G := G) S00 S01 S10 S11 :=
  nontrivialKummerEvaluation (I := I) (G := G) D.square

/-- The actual IPLActual from the combined packet. -/
def nontrivialIplOfPacket
    (D : NontrivialKummerIPLSource (I := I) (G := G)) :
    IPLActual (G := G) S10 S10 S00 S01 S11 :=
  nontrivialIpl (I := I) (G := G) D.ipl

/-- The exact missing square source fields: upper evaluation, left Kummer,
right Kummer, and lower unit portion. -/
def MissingSquareArrows
    (D : NontrivialKummerIPLSource (I := I) (G := G)) : Prop :=
  (Nonempty (SourceEvaluationArrow G S00 S01) ∧
    Nonempty (SourceKummerArrow G S10 S00) ∧
    Nonempty (SourceKummerArrow G S11 S01) ∧
    Nonempty (SourceEvaluationUnitPortion G S10 S11))

/-- The exact missing IPL arrow fields. -/
def MissingIPLArrows
    (D : NontrivialKummerIPLSource (I := I) (G := G)) : Prop :=
  (Nonempty (SourceKummerArrow G S00 S01) ∧
    Nonempty (SourceEvaluationArrow G S01 S11))

end LeanFormal.IUT.XiFPaper.NontrivialKummerEvaluationActualAdapted

end
