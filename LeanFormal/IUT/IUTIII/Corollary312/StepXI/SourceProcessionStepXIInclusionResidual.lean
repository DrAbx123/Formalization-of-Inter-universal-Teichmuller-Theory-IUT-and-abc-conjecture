import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceProcessionStepXIMinimalForm
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiring
import Mathlib.Tactic

/-!
# Residual attack on the single (xi-f) inclusion `q <= hullValue` (Card-STEPXI-XIF-INCLUSION)

Downdrill record (2026-10-16).  The pinned Step-XI comparison form
(`SourceProcessionStepXI.lean`, section "V2 pinned comparison form";
`SourceProcessionStepXIMinimalForm.lean`) reduces the corpus two-term comparison
of Steps (xi-d)/(xi-f) to the single named real inclusion `q <= hullValue` with
`q < 0`.  In the corpus `hullValue = -|log(Theta)|` is the *negative* log-volume
of the holomorphic hull.

Corpus anchors (IUT III, Corollary 3.12 proof, Step (xi)):

* (xi-d), III:10843-10848: `R^{<= -|log(Theta)|} := {lambda in R | lambda <=
  -|log(Theta)|} subset R; -|log(q)| in R`, where `-|log(Theta)|` is by definition
  the (negative) log-volume of `1,circ U`.
* (xi-f), III:10895-10898: the inclusion `-|log(q)| in R^{<= -|log(Theta)|}`,
  hence the inequality `-|log(q)| <= -|log(Theta)| in R`, i.e. `C_Theta >= -1`,
  follows formally.

Route results (proofs in this file):

* Route 1 (V2-constructor side): **closed, degenerate.**  Every real hull
  carrier available in the tree is nonnegative (`iqHullRealVolume_nonneg`,
  `CertificateHullWiring.lean:93`; `sourceRealHullVolume_nonneg`, :251), and
  every in-tree q candidate is negative.  Hence the literal inclusion holds with
  no hull-side input: `negativeValue_le_of_nonnegative` plus its carrier
  instances.  The pinned V2 link and the assembled V2 boundary conclusion are
  wired from nonnegativity alone; the closure consumes no information about the
  carrier value (zero discriminating power).

* Route 2 (hull-side reverse estimates): **blocked.**  A non-degenerate reading
  of the card needs a signed carrier (`hullValue = -|log(Theta)| < 0`).  No
  donor exists: the IQ interface exposes an `ENNReal`-valued log-volume
  (`SourceHullCompactnessReduction.lean:52-81`, real part `>= 0`), and under
  pointwise degree faithfulness no finite real upper value exists
  (`sourceThetaBound_unsat_of_degreeFaithful`, `CertificateHullWiring.lean:302`,
  via `sourceHullVolume_eq_top_of_degreeFaithful`) -- the same incompatibility
  as `SourceHullInterfaceDischarge.lean:232-240`.

* Route 3 (negative-result probe): **done.**  On signed values the inclusion is
  not forced by the sign constraints
  (`xifInclusion_signedSurface_counterexample`); the genuine content lives on
  the missing signed carrier.  The residual named input is recorded in the
  audit ledger (`sourceProcessionStepXIXifInclusionResidual`).

Nothing here constructs the signed carrier (intersection with Card-HULLREAL).
Every wire below is a reduced/pinned-form closure of the literal inclusion;
consumers must cite it with that label and must not use it as the corpus-signed
comparison `C_Theta >= -1`.
-/

namespace LeanFormal.IUT

noncomputable section

/-! ## 1. Scalar degeneracy and the signed-surface counterexample -/

namespace SourceStepXIXifInclusionResidual

/-- Degeneracy lemma: a negative real is below every nonnegative real.  This is
the entire content of the (xi-f)-shaped inclusion on a nonnegative carrier; it
consumes no information about the carrier's value. -/
theorem negativeValue_le_of_nonnegative {q hullValue : Real} (hq : q < 0)
    (hh : 0 ≤ hullValue) : q ≤ hullValue :=
  le_trans hq.le hh

/-- Negative-result probe on the signed surface: the (xi-f)-shaped inclusion is
not a consequence of the sign constraints alone.  For the corpus sign
(`hullValue = -|log(Theta)| < 0`) the comparison carries genuine content, so no
sign-level argument can produce it; conversely on nonnegative carriers it is
the degeneracy lemma above. -/
theorem xifInclusion_signedSurface_counterexample :
    ∃ q hullValue : Real, q < 0 ∧ hullValue < 0 ∧ ¬ q ≤ hullValue :=
  ⟨-1, -2, by norm_num, by norm_num, by norm_num⟩

end SourceStepXIXifInclusionResidual

open SourceProcessionBoundary
open MultiradialKernel
open MultiradialKernel.Core
open ParametricTheorem311
open ParametricDStage
open ParametricStepXI

/-! ## 2. Route 1: degenerate closure on the in-tree nonnegative carriers -/

namespace SourceProcessionStepXI

universe u v w

variable {l : PrimeGeFive} {V : Type v}
variable {Label : Type u} {Choice : Type w} [AddGroup Label]

variable (input : SourceProcessionBoundary.Input (l := l) (V := V)
  (Label := Label) (Choice := Choice))

open SourceStepXIXifInclusionResidual

/-- Interface-side carrier instance: any negative real is below the real part of
the hull log-volume of any interface realization, because that real part is an
`ENNReal.toReal` and hence nonnegative. -/
theorem negativeValue_le_iqHullRealVolume {X : Type u}
    (W : IQHullLogVolumeInterface X) {q : Real} (hq : q < 0) :
    q ≤ iqHullRealVolume W :=
  negativeValue_le_of_nonnegative hq (iqHullRealVolume_nonneg W)

/-- Route-1 wire, generic nonnegative carrier: the pinned V2 link from
nonnegativity of the hull value alone; no inclusion hypothesis remains. -/
def arithmeticLinkV2OfNonnegativeHullValue (route : List (RouteStep Label))
    (q hullValue : Real) (hq : q < 0) (hh : 0 ≤ hullValue)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :
    ArithmeticLinkV2 input route :=
  arithmeticLinkV2OfHullInclusion input route q hullValue hq
    (negativeValue_le_of_nonnegative hq hh) ipl she apt
    ipl_evidence she_evidence apt_evidence

/-- Route-1 wire on an IQ-interface carrier `W`: the (xi-f) inclusion is
discharged by `iqHullRealVolume_nonneg`; no hull-side estimate is consumed. -/
def arithmeticLinkV2OfIqHullRealVolume (route : List (RouteStep Label))
    {X : Type u} (W : IQHullLogVolumeInterface X) (q : Real) (hq : q < 0)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :
    ArithmeticLinkV2 input route :=
  arithmeticLinkV2OfHullInclusion input route q (iqHullRealVolume W) hq
    (negativeValue_le_iqHullRealVolume W hq) ipl she apt
    ipl_evidence she_evidence apt_evidence

/-- Route-1 wire with the compiled absolute-degree-normalized signed q-log as
`q`: its negativity is proved from the nonempty selection
(`normalizedLowerSignedLog_neg`), and the inclusion follows from the nonnegative
hull value. -/
def arithmeticLinkV2OfNonnegativeHullValueOfAbsoluteDegreeNormalizedSignedLog
    (route : List (RouteStep Label))
    {k : Type*} [Field k] [NumberField k]
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) ->
      NumberFieldFinitePlace.FinitePlaceQCandidate lowerPlace.val)
    (selected_nonempty : selectedLowerPlaces.Nonempty)
    (hullValue : Real) (hh : 0 ≤ hullValue)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :
    ArithmeticLinkV2 input route :=
  arithmeticLinkV2OfNonnegativeHullValue input route
    (ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
      selectedLowerPlaces parameters)
    hullValue
    (ArithmeticQPilotGlobalNormalization.normalizedLowerSignedLog_neg
      selectedLowerPlaces parameters selected_nonempty)
    hh ipl she apt ipl_evidence she_evidence apt_evidence

/-- Link-level conclusion of the route-1 wire. -/
theorem arithmeticLinkV2OfNonnegativeHullValue_conclusion
    (route : List (RouteStep Label))
    (q hullValue : Real) (hq : q < 0) (hh : 0 ≤ hullValue)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :
    Cor312Conclusion
      ((arithmeticLinkV2OfNonnegativeHullValue input route q hullValue hq hh
        ipl she apt ipl_evidence she_evidence apt_evidence).arithmetic.toContract) :=
  (arithmeticLinkV2OfNonnegativeHullValue input route q hullValue hq hh
    ipl she apt ipl_evidence she_evidence apt_evidence).arithmetic.conclusion

/-- Boundary-level conclusion of the route-1 wire (assembled V2 boundary). -/
theorem sourceStepXIBoundaryV2_contract_of_nonnegativeHull
    (route : List (RouteStep Label))
    (q hullValue : Real) (hq : q < 0) (hh : 0 ≤ hullValue)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :
    Cor312Conclusion
      (sourceStepXIBoundaryV2 input route
        (arithmeticLinkV2OfNonnegativeHullValue input route q hullValue hq hh
          ipl she apt ipl_evidence she_evidence apt_evidence)).assembly.arithmetic.toContract :=
  sourceStepXIBoundaryV2_contract input route _

end SourceProcessionStepXI

/-! ## 3. Value-side carrier: the same degenerate closure -/

namespace Theorem311Source
namespace OriginalInput

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}

variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Value-side carrier instance: the real part of the value-realized hull
log-volume is nonnegative, so the (xi-f) inclusion is again automatic for
negative q. -/
theorem negativeValue_le_sourceRealHullVolume (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) {q : Real}
    (hq : q < 0) :
    q ≤ I.sourceRealHullVolume v R n :=
  le_trans hq.le (I.sourceRealHullVolume_nonneg v R n)

end OriginalInput
end Theorem311Source

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Residual card of the single (xi-f) inclusion (Card-STEPXI-XIF-INCLUSION).
The literal pinned inclusion closes degenerately on the in-tree nonnegative
carriers (`SourceProcessionStepXI.arithmeticLinkV2OfNonnegativeHullValue` and
`Theorem311Source.OriginalInput.negativeValue_le_sourceRealHullVolume`), while
the corpus-signed reading (`hullValue = -|log(Theta)| < 0`, III:10846-10848)
requires a signed hull-log-volume carrier carrying the genuine comparison
content of III:10895-10898.  No such carrier exists in the tree: the IQ
interface exposes only an `ENNReal`-valued log-volume
(`SourceHullCompactnessReduction.lean:62`), and under degree faithfulness no
finite real upper value exists
(`sourceThetaBound_unsat_of_degreeFaithful`, `CertificateHullWiring.lean:302`). -/
def sourceProcessionStepXIXifInclusionResidual : Obligation :=
  { id := "IUT-III.source-procession-stepXI-xif-inclusion"
    source := "IUT III, Corollary 3.12 proof, Steps (xi-d)-(xi-f) (III:10843-10898)"
    status := VerificationStatus.interface
    note :=
      "Pinned single inclusion q <= hullValue. Literal form closed " ++
        "degenerately on the nonnegative in-tree carriers (nonnegativity " ++
        "alone; zero discriminating power). Corpus-signed form " ++
        "(-|log(Theta)| < 0, III:10846-10848) has no donor: IQ interface " ++
        "logVolume is ENNReal-valued, and degree faithfulness kills finite " ++
        "real upper values (sourceThetaBound_unsat_of_degreeFaithful). " ++
        "Residual = signed hull-log-volume carrier + genuine comparison " ++
        "content; intersects Card-HULLREAL. Wires are reduced/pinned form, " ++
        "not the corpus C_Theta >= -1 statement."
    dependsOn :=
      [ "IUT-III.source-procession-stepXI-boundary" ] }

end LeanFormal.IUT.Audit
