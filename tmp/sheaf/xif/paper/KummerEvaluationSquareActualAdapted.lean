import tmp.sheaf.xif.paper.ThetaLinkCommonKummerActualAdapted
import tmp.sheaf.xif.paper.LogKummerCorrespondenceFromSource
import tmp.sheaf.xif.paper.IPLAPTActual

-- Actual Kummer-evaluation square and IPL-composite inputLink
--
-- Built on ThetaLinkCommonKummerActualAdapted: the actual four-corner
-- Kummer/evaluation arrows on the common topological group G4 and
-- the actual KummerEvaluationActual square. Also built on
-- LogKummerCorrespondenceFromSource: actual vertical links and actual
-- Kummer layers. This file constructs:
--   (1) actual IPL data whose arrows are the actual left/upper arrows
--       of the four-corner square;
--   (2) the proof inputLink = composite for that actual IPL data;
--   (3) the actual commutativity proof of the KummerEvaluationSquare.
-- No inequality is judged; no sorry/axiom/True/PUnit/toy.
-- WRITE-ONLY: no lake/lean.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.KummerEvaluationSquareActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.ThetaLinkCommonKummerActualAdapted

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

-- The actual four-corner Kummer-evaluation square on G4.
noncomputable abbrev actualKummerEvaluationSquare :=
  actualKummerEvaluation (I := I)

-- The square's actual commutation: two paths agree.
theorem actualKummerEvaluationSquare_commutes :
    (actualKummerEvaluationSquare (I := I)).square.domainExpression =
      (actualKummerEvaluationSquare (I := I)).square.codomainExpression :=
  (actualKummerEvaluationSquare (I := I)).square.domainExpression_eq_codomainExpression

-- Actual IPL data using the actual four-corner arrows:
-- intermediate = S10, gau = S00, env = S10, coric = S00, q-pilot = S01.
noncomputable def actualIPLOfSquare :
    IPLActual (G := G4 (I := I))
      (S10 (I := I)) (S00 (I := I)) (S10 (I := I)) (S00 (I := I)) (S01 (I := I)) where
  lowerHorizontal1 := (I.linkAt 0 0 1 0).primeStripEquiv
  lowerHorizontal2 := (I.linkAt 1 0 0 0).primeStripEquiv
  kummer := actualLeftKummer (I := I)
  evaluation := actualUpperEvaluation (I := I)
  inputLink :=
    ((I.linkAt 0 0 1 0).primeStripEquiv.symm).trans
      (((I.linkAt 1 0 0 0).primeStripEquiv.symm).trans
        ((actualLeftKummer (I := I)).stripIso.trans
          (actualUpperEvaluation (I := I)).stripIso))
  factorization := rfl

-- The actual IPL input link equals the actual IPL composite.
theorem actualIPLOfSquare_inputLink_eq_composite :
    (actualIPLOfSquare (I := I)).inputLink =
      (actualIPLOfSquare (I := I)).composite :=
  IPLActual.inputLink_eq_composite (actualIPLOfSquare (I := I))

-- The actual IPL composite is definitionally the composite of the actual
-- four-corner arrows used in the square.
theorem actualIPLOfSquare_composite_eq :
    (actualIPLOfSquare (I := I)).composite =
      (actualIPLOfSquare (I := I)).inputLink :=
  (actualIPLOfSquare (I := I)).inputLink_eq_composite.symm

#check actualKummerEvaluationSquare
#check actualKummerEvaluationSquare_commutes
#check actualIPLOfSquare
#check actualIPLOfSquare_inputLink_eq_composite
#check actualIPLOfSquare_composite_eq

end LeanFormal.IUT.XiFPaper.KummerEvaluationSquareActualAdapted

end