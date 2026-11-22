import LeanFormal.IUT.IUTIII.Theorem311.SourceFTimesMuPrimeStripPolyIsomorphism
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows

/-!
# The actual (1,0) q-pilot F^boxplus-triangleright-x-mu-prime-strip candidate

Source: IUT II, Corollary 4.10, (i), pp. 158-159: the F^boxplus-prime-strip
associated to the F-prime-strip of a Theta-pm-ellNF-Hodge theater; (iii), p. 159:
the associated F^boxplus-triangleright-x-mu-prime-strip.  IUT II, Definition 4.9,
(viii): the x-mu-prime-strip data.  IUT III, Definition 3.8, (i), pp. 112-113
(iut3.txt lines 6748-6769): the q-pilot object is the object of the global
realified Frobenioid determined by the q_v, v in V_bad; IUT III, p. 16: its
log-volume is -|log q|.

This file constructs the actual candidate object at (1,0) obtained by the
canonical times-mu construction of IUT II, Corollary 4.10, (iii), from the actual
(1,0) F-prime-strip of the source input:

* qPilotFTimesMuPrimeStripAt10Actual: the canonical SourceFTimesMuPrimeStrip of
  the actual (1,0) F-prime-strip;
* its underlying F-prime-strip is exactly the actual (1,0) F-prime-strip;
* its x-mu fiber at v is the torsion quotient TimesMuQuotient of the actual unit
  group, with the actual quotient map, its surjectivity and kernel, the descended
  units action and the degree law.

This is the actual candidate strip data, not the paper q-pilot
F^boxplus-triangleright-x-mu-prime-strip: the identification with the codomain
strip of the Theta-times-mu LGP-link is the exact missing object recorded in
S3133QPilotPaperMissingActual.  No inequality is asserted.  No toy/True/PUnit/
axiom/sorry.  WRITE-ONLY; no local compile; queued.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3133QPilotFTimesMuCandidateActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The actual (1,0) candidate F^boxplus-triangleright-x-mu-prime-strip: the
canonical times-mu prime-strip of the actual (1,0) F-prime-strip (IUT II,
Corollary 4.10, (iii)). -/
noncomputable def qPilotFTimesMuPrimeStripAt10Actual :
    SourceFTimesMuPrimeStrip V :=
  SourceFTimesMuPrimeStrip.canonical (I.fPrimeStripAt 1 0)

/-- The candidate's underlying F-prime-strip is exactly the actual (1,0)
F-prime-strip. -/
theorem qPilotFTimesMuPrimeStripAt10Actual_toFPrimeStrip :
    (qPilotFTimesMuPrimeStripAt10Actual I).toFPrimeStrip =
      I.fPrimeStripAt 1 0 := rfl

/-- The candidate's x-mu fiber at v is the actual torsion quotient of the actual
unit group at v (IUT II, Definition 4.9, (v), (viii)). -/
theorem qPilotFTimesMuPrimeStripAt10Actual_timesMu (v : V) :
    (qPilotFTimesMuPrimeStripAt10Actual I).timesMu v =
      TimesMuQuotient ((I.fPrimeStripAt 1 0).Mon v)ˣ := rfl

/-- The candidate's quotient map at v is the actual torsion quotient map. -/
theorem qPilotFTimesMuPrimeStripAt10Actual_quotientMap (v : V) :
    (qPilotFTimesMuPrimeStripAt10Actual I).timesMuQuotientMap v =
      TimesMuQuotient.quotientMap := rfl

/-- The candidate's quotient map at v is surjective. -/
theorem qPilotFTimesMuPrimeStripAt10Actual_quotientMap_surjective (v : V) :
    Function.Surjective
      ((qPilotFTimesMuPrimeStripAt10Actual I).timesMuQuotientMap v) :=
  (qPilotFTimesMuPrimeStripAt10Actual I).timesMuQuotientMap_surjective v

/-- The kernel of the candidate's quotient map at v is the torsion subgroup of
the actual unit group. -/
theorem qPilotFTimesMuPrimeStripAt10Actual_quotientMap_ker (v : V) :
    MonoidHom.ker ((qPilotFTimesMuPrimeStripAt10Actual I).timesMuQuotientMap v) =
      CommGroup.torsion ((I.fPrimeStripAt 1 0).Mon v)ˣ :=
  (qPilotFTimesMuPrimeStripAt10Actual I).timesMuQuotientMap_ker v

/-- The candidate's descended x-mu action at v is the actual quotient action. -/
theorem qPilotFTimesMuPrimeStripAt10Actual_timesMuAction (v : V) :
    (qPilotFTimesMuPrimeStripAt10Actual I).timesMuAction v =
      (I.fPrimeStripAt 1 0).timesMuAction v := rfl

/-- The candidate's x-mu action is compatible with the quotient map and the
actual units action on the (1,0) strip. -/
theorem qPilotFTimesMuPrimeStripAt10Actual_action_quotientMap
    (v : V) (g : (I.fPrimeStripAt 1 0).toDPrimeStrip.Pi v)
    (u : ((I.fPrimeStripAt 1 0).Mon v)ˣ) :
    (qPilotFTimesMuPrimeStripAt10Actual I).timesMuAction v g
        ((qPilotFTimesMuPrimeStripAt10Actual I).timesMuQuotientMap v u) =
      (qPilotFTimesMuPrimeStripAt10Actual I).timesMuQuotientMap v
        (FPrimeStrip.unitsAction (I.fPrimeStripAt 1 0) v g u) :=
  (qPilotFTimesMuPrimeStripAt10Actual I).timesMuAction_quotientMap v g u

/-- The candidate's x-mu degree at v is the actual descended degree. -/
theorem qPilotFTimesMuPrimeStripAt10Actual_timesMuDegree (v : V) :
    (qPilotFTimesMuPrimeStripAt10Actual I).timesMuDegree v =
      (I.fPrimeStripAt 1 0).timesMuDegreeOfUnits v := rfl

/-- The candidate's x-mu degree is compatible with the quotient map and the
actual degree on units of the (1,0) strip. -/
theorem qPilotFTimesMuPrimeStripAt10Actual_degree_quotientMap
    (v : V) (u : ((I.fPrimeStripAt 1 0).Mon v)ˣ) :
    (qPilotFTimesMuPrimeStripAt10Actual I).timesMuDegree v
        ((qPilotFTimesMuPrimeStripAt10Actual I).timesMuQuotientMap v u) =
      (I.fPrimeStripAt 1 0).degree v (u : (I.fPrimeStripAt 1 0).Mon v) :=
  (qPilotFTimesMuPrimeStripAt10Actual I).timesMuDegree_quotientMap v u

/-- The candidate times-mu prime-strip carries all the data of the actual (1,0)
F-prime-strip together with its actual x-mu quotient data. -/
theorem qPilotFTimesMuPrimeStripAt10Actual_data :
    (qPilotFTimesMuPrimeStripAt10Actual I).toFPrimeStrip = I.fPrimeStripAt 1 0 ∧
      (∀ v,
        (qPilotFTimesMuPrimeStripAt10Actual I).timesMu v =
          TimesMuQuotient ((I.fPrimeStripAt 1 0).Mon v)ˣ) ∧
      (∀ v,
        Function.Surjective
          ((qPilotFTimesMuPrimeStripAt10Actual I).timesMuQuotientMap v)) :=
  ⟨rfl, fun v => rfl, fun v =>
    (qPilotFTimesMuPrimeStripAt10Actual I).timesMuQuotientMap_surjective v⟩

end LeanFormal.IUT.XiFPaper.S3133QPilotFTimesMuCandidateActual
