import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ParametricStepXI
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.FiniteCertificateBridge
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceProcessionStepXI
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.Volume
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotGlobalNormalization

/-!
# Source-facing reductions of the Step-XI contract and certificate fields

This module implements the Step-XI north-wall reductions that are provable from
the already compiled interface layer, and it isolates the remaining source cards
(see `logs/coordination/stepxi-contract-reduction-20261016.md` for the field
table and the named cards).

Proved here:

* `StepXIFiniteCertificate.ofHullWeights` / `StepXIFiniteCertificate.ofHullUniform`:
  define the weighted values to be the hull volumes, so that the certificate
  field `weighted_matches_hull` is `rfl`; the uniform specialization also
  discharges `weights_nonnegative`.  The entire certificate then reduces to a
  hull, the two scalars `q`, `theta`, the two comparison fields, and `q < 0`.
* `StepXIFiniteCertificate.ofAbsoluteDegreeNormalizedSignedLog`,
  `StepXIContract.ofAbsoluteDegreeNormalizedSignedLog`,
  `ParametricStepXI.stepXIInputOfAbsoluteDegreeNormalizedSignedLog`: instantiate
  the scalar `q` by the actual absolute-degree-normalized signed q-log
  `ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog`
  of an actual finite-place q-family.  The field `q_negative` (resp. the
  `q_negative` component) is then proved from a nonempty finite selection, and
  the only arithmetic input left is the named object-level inequality
  `absoluteDegreeNormalizedLowerSignedLog ... <= target` (resp. `<= hull volume`).
  The identification of this quantity with the paper's actual q-pilot is NOT
  asserted.
* `finiteLinkEvidenceOfHullTarget`: with the target chosen as the hull volume,
  the two real comparison fields of `FiniteStepXILinkEvidence` are exactly the
  certificate's own `q_le_hull` and `hull_le_theta`; the only remaining inputs
  are the IPL/SHE/APT propositions and their evidence.
* `SourceProcessionStepXI.arithmeticLinkOfStepXIInput` and
  `arithmetic_output_eq_wall_theorem311`: the `arithmetic_source` wire of
  `ArithmeticLink` is definitional (both sides equal `runAlgorithm`), and the
  three arithmetic fields are projections of the `StepXIInput`; the whole link
  reduces to its input, with no remaining wire obligation.
* `SourceProcessionStepXI.arithmeticLinkOfAbsoluteDegreeNormalizedSignedLog`: the
  composed source-procession link whose only remaining fields are the two named
  real inequalities and the IPL/SHE/APT evidence.

Not proved here (named source cards): the IPL/SHE/APT content, the amplitude
bound `hull volume <= theta` at the actual source carrier, and the source-facing
realization of the hull log-volume interface.  No existence of a contract or a
certificate is asserted, and no existing statement is weakened.
-/

namespace LeanFormal.IUT

noncomputable section

/-! ## 1. `StepXIFiniteCertificate`: value/weight bookkeeping is definitional -/

namespace StepXIFiniteCertificate

/-- Certificate constructor in which the weighted values are defined to be the
hull volumes: `weighted_matches_hull` is then `rfl` and disappears from the
input surface.  The remaining weight content is exactly the weight function,
its total, nonnegativity, the two real comparison fields, and `q < 0`. -/
def ofHullWeights {label : Type*} [Fintype label]
    (hull : FiniteHull label)
    (weight : label -> Real) (weightTotal : Real)
    (weightTotal_pos : 0 < weightTotal)
    (weightTotal_eq_sum : weightTotal = Finset.univ.sum weight)
    (weights_nonnegative : forall i, 0 <= weight i)
    (qSigned thetaSigned : Real)
    (q_le_hull : qSigned <= hull.hullVolume)
    (hull_le_theta : hull.hullVolume <= thetaSigned)
    (q_negative : qSigned < 0) :
    StepXIFiniteCertificate label where
  hull := hull
  weighted :=
    { value := hull.volume
      weight := weight
      weightTotal := weightTotal
      weightTotal_pos := weightTotal_pos
      weightTotal_eq_sum := weightTotal_eq_sum }
  weighted_matches_hull := fun _ => rfl
  weights_nonnegative := weights_nonnegative
  qSigned := qSigned
  thetaSigned := thetaSigned
  q_le_hull := q_le_hull
  hull_le_theta := hull_le_theta
  q_negative := q_negative

@[simp] theorem ofHullWeights_qSigned {label : Type*} [Fintype label]
    (hull : FiniteHull label)
    (weight : label -> Real) (weightTotal : Real)
    (weightTotal_pos : 0 < weightTotal)
    (weightTotal_eq_sum : weightTotal = Finset.univ.sum weight)
    (weights_nonnegative : forall i, 0 <= weight i)
    (qSigned thetaSigned : Real)
    (q_le_hull : qSigned <= hull.hullVolume)
    (hull_le_theta : hull.hullVolume <= thetaSigned)
    (q_negative : qSigned < 0) :
    (ofHullWeights hull weight weightTotal weightTotal_pos weightTotal_eq_sum
      weights_nonnegative qSigned thetaSigned q_le_hull hull_le_theta
      q_negative).qSigned = qSigned := rfl

@[simp] theorem ofHullWeights_thetaSigned {label : Type*} [Fintype label]
    (hull : FiniteHull label)
    (weight : label -> Real) (weightTotal : Real)
    (weightTotal_pos : 0 < weightTotal)
    (weightTotal_eq_sum : weightTotal = Finset.univ.sum weight)
    (weights_nonnegative : forall i, 0 <= weight i)
    (qSigned thetaSigned : Real)
    (q_le_hull : qSigned <= hull.hullVolume)
    (hull_le_theta : hull.hullVolume <= thetaSigned)
    (q_negative : qSigned < 0) :
    (ofHullWeights hull weight weightTotal weightTotal_pos weightTotal_eq_sum
      weights_nonnegative qSigned thetaSigned q_le_hull hull_le_theta
      q_negative).thetaSigned = thetaSigned := rfl

/-- Uniform-weight specialization of `ofHullWeights`: the certificate input
surface is exactly a hull, the two scalars `q`, `theta`, the two comparison
inequalities, and `q < 0`; both weight fields are discharged. -/
def ofHullUniform {label : Type*} [Fintype label] [Nonempty label]
    (hull : FiniteHull label)
    (qSigned thetaSigned : Real)
    (q_le_hull : qSigned <= hull.hullVolume)
    (hull_le_theta : hull.hullVolume <= thetaSigned)
    (q_negative : qSigned < 0) :
    StepXIFiniteCertificate label :=
  ofHullWeights hull (fun _ => (1 : Real)) (Fintype.card label : Real)
    (by exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance))
    (by simp)
    (fun _ => zero_le_one)
    qSigned thetaSigned q_le_hull hull_le_theta q_negative

@[simp] theorem ofHullUniform_qSigned {label : Type*} [Fintype label]
    [Nonempty label]
    (hull : FiniteHull label)
    (qSigned thetaSigned : Real)
    (q_le_hull : qSigned <= hull.hullVolume)
    (hull_le_theta : hull.hullVolume <= thetaSigned)
    (q_negative : qSigned < 0) :
    (ofHullUniform hull qSigned thetaSigned q_le_hull hull_le_theta
      q_negative).qSigned = qSigned := rfl

@[simp] theorem ofHullUniform_thetaSigned {label : Type*} [Fintype label]
    [Nonempty label]
    (hull : FiniteHull label)
    (qSigned thetaSigned : Real)
    (q_le_hull : qSigned <= hull.hullVolume)
    (hull_le_theta : hull.hullVolume <= thetaSigned)
    (q_negative : qSigned < 0) :
    (ofHullUniform hull qSigned thetaSigned q_le_hull hull_le_theta
      q_negative).thetaSigned = thetaSigned := rfl

/-- Certificate constructor with the scalar `q` instantiated by the actual
absolute-degree-normalized signed q-log of an actual finite-place q-family.
The negativity `q < 0` is proved from the nonempty selection
(`ArithmeticQPilotGlobalNormalization.normalizedLowerSignedLog_neg`); the only
arithmetic input is the named object-level inequality
`q <= hull volume`.  The amplitude field `hull volume <= theta` remains an
explicit input (the amplitude card). -/
def ofAbsoluteDegreeNormalizedSignedLog
    {label : Type*} [Fintype label] [Nonempty label]
    {k : Type*} [Field k] [NumberField k]
    (hull : FiniteHull label)
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) ->
      NumberFieldFinitePlace.FinitePlaceQCandidate lowerPlace.val)
    (selected_nonempty : selectedLowerPlaces.Nonempty)
    (thetaSigned : Real)
    (hull_le_theta : hull.hullVolume <= thetaSigned)
    (q_le_hull :
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
        selectedLowerPlaces parameters <= hull.hullVolume) :
    StepXIFiniteCertificate label :=
  ofHullUniform hull
    (ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
      selectedLowerPlaces parameters)
    thetaSigned q_le_hull hull_le_theta
    (ArithmeticQPilotGlobalNormalization.normalizedLowerSignedLog_neg
      selectedLowerPlaces parameters selected_nonempty)

@[simp] theorem ofAbsoluteDegreeNormalizedSignedLog_qSigned
    {label : Type*} [Fintype label] [Nonempty label]
    {k : Type*} [Field k] [NumberField k]
    (hull : FiniteHull label)
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) ->
      NumberFieldFinitePlace.FinitePlaceQCandidate lowerPlace.val)
    (selected_nonempty : selectedLowerPlaces.Nonempty)
    (thetaSigned : Real)
    (hull_le_theta : hull.hullVolume <= thetaSigned)
    (q_le_hull :
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
        selectedLowerPlaces parameters <= hull.hullVolume) :
    (ofAbsoluteDegreeNormalizedSignedLog hull selectedLowerPlaces parameters
      selected_nonempty thetaSigned hull_le_theta q_le_hull).qSigned =
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
        selectedLowerPlaces parameters := rfl

end StepXIFiniteCertificate

/-! ## 2. `FiniteStepXILinkEvidence`: the hull target discharges both comparison fields -/

/-- The two real comparison fields of `FiniteStepXILinkEvidence` are supplied by
the certificate itself when the target is the hull volume: `q_le_target` is
`certificate.q_le_hull` and `target_le_theta` is `certificate.hull_le_theta`.
Hence the only remaining inputs of the link evidence over a certificate are the
IPL/SHE/APT propositions and their evidence. -/
def finiteLinkEvidenceOfHullTarget {label : Type*} [Fintype label]
    (certificate : StepXIFiniteCertificate label)
    (ipl she apt : Prop) (ipl_evidence : ipl)
    (she_evidence : she) (apt_evidence : apt) :
    FiniteStepXILinkEvidence certificate where
  targetSigned := certificate.hull.hullVolume
  ipl := ipl
  she := she
  apt := apt
  ipl_evidence := ipl_evidence
  she_evidence := she_evidence
  apt_evidence := apt_evidence
  q_le_target := certificate.q_le_hull
  target_le_theta := certificate.hull_le_theta

@[simp] theorem finiteLinkEvidenceOfHullTarget_targetSigned
    {label : Type*} [Fintype label]
    (certificate : StepXIFiniteCertificate label)
    (ipl she apt : Prop) (ipl_evidence : ipl)
    (she_evidence : she) (apt_evidence : apt) :
    (finiteLinkEvidenceOfHullTarget certificate ipl she apt ipl_evidence
      she_evidence apt_evidence).targetSigned =
      certificate.hull.hullVolume := rfl

/-- The Corollary-3.12 conclusion of the finite bridge from a certificate and
the IPL/SHE/APT evidence alone: no further real inequality is needed in the
link evidence. -/
theorem cor312Conclusion_of_hullTargetLinkEvidence {label : Type*}
    [Fintype label]
    (certificate : StepXIFiniteCertificate label)
    (ipl she apt : Prop) (ipl_evidence : ipl)
    (she_evidence : she) (apt_evidence : apt) :
    Cor312Conclusion
      (certificate.toContract
        (finiteLinkEvidenceOfHullTarget certificate ipl she apt ipl_evidence
          she_evidence apt_evidence)) :=
  cor312_of_finite_certificate certificate
    (finiteLinkEvidenceOfHullTarget certificate ipl she apt ipl_evidence
      she_evidence apt_evidence)

/-! ## 3. `StepXIContract` with the actual q-log -/

namespace StepXIContract

/-- The contract constructor with `qSigned` instantiated by the actual
absolute-degree-normalized signed q-log; `q_negative` is proved from the
nonempty finite selection.  The unprovable remainder is exactly: the two real
comparisons (in particular the named inequality `q <= target`), and the
IPL/SHE/APT propositions with their evidence. -/
def ofAbsoluteDegreeNormalizedSignedLog
    {k : Type*} [Field k] [NumberField k]
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) ->
      NumberFieldFinitePlace.FinitePlaceQCandidate lowerPlace.val)
    (selected_nonempty : selectedLowerPlaces.Nonempty)
    (targetSigned thetaSigned : Real)
    (q_le_target :
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
        selectedLowerPlaces parameters <= targetSigned)
    (target_le_theta : targetSigned <= thetaSigned)
    (ipl she apt : Prop) (ipl_evidence : ipl)
    (she_evidence : she) (apt_evidence : apt) :
    StepXIContract where
  qSigned :=
    ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
      selectedLowerPlaces parameters
  thetaSigned := thetaSigned
  targetSigned := targetSigned
  q_negative :=
    ArithmeticQPilotGlobalNormalization.normalizedLowerSignedLog_neg
      selectedLowerPlaces parameters selected_nonempty
  ipl := ipl
  she := she
  apt := apt
  ipl_evidence := ipl_evidence
  she_evidence := she_evidence
  apt_evidence := apt_evidence
  q_le_target := q_le_target
  target_le_theta := target_le_theta

@[simp] theorem ofAbsoluteDegreeNormalizedSignedLog_qSigned
    {k : Type*} [Field k] [NumberField k]
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) ->
      NumberFieldFinitePlace.FinitePlaceQCandidate lowerPlace.val)
    (selected_nonempty : selectedLowerPlaces.Nonempty)
    (targetSigned thetaSigned : Real)
    (q_le_target :
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
        selectedLowerPlaces parameters <= targetSigned)
    (target_le_theta : targetSigned <= thetaSigned)
    (ipl she apt : Prop) (ipl_evidence : ipl)
    (she_evidence : she) (apt_evidence : apt) :
    (ofAbsoluteDegreeNormalizedSignedLog selectedLowerPlaces parameters
      selected_nonempty targetSigned thetaSigned q_le_target target_le_theta
      ipl she apt ipl_evidence she_evidence apt_evidence).qSigned =
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
        selectedLowerPlaces parameters := rfl

end StepXIContract

/-! ## 4. `StepXIInput` with the actual q-log -/

namespace ParametricStepXI

open ParametricTheorem311

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label]

/-- The `StepXIInput` of the parametric Step-XI assembly with `qSigned`
instantiated by the actual absolute-degree-normalized signed q-log and
`output` the algorithm run; `q_negative` is proved from the nonempty finite
selection. -/
def stepXIInputOfAbsoluteDegreeNormalizedSignedLog
    (carrier : Carrier Label Choice) (input : AlgorithmInput carrier)
    {k : Type*} [Field k] [NumberField k]
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) ->
      NumberFieldFinitePlace.FinitePlaceQCandidate lowerPlace.val)
    (selected_nonempty : selectedLowerPlaces.Nonempty)
    (targetSigned thetaSigned : Real)
    (q_le_target :
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
        selectedLowerPlaces parameters <= targetSigned)
    (target_le_theta : targetSigned <= thetaSigned)
    (ipl she apt : Prop) (ipl_evidence : ipl)
    (she_evidence : she) (apt_evidence : apt) :
    StepXIInput carrier input :=
  stepXIInput carrier input
    (ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
      selectedLowerPlaces parameters)
    targetSigned thetaSigned
    (ArithmeticQPilotGlobalNormalization.normalizedLowerSignedLog_neg
      selectedLowerPlaces parameters selected_nonempty)
    ipl she apt ipl_evidence she_evidence apt_evidence
    q_le_target target_le_theta

@[simp] theorem stepXIInputOfAbsoluteDegreeNormalizedSignedLog_qSigned
    (carrier : Carrier Label Choice) (input : AlgorithmInput carrier)
    {k : Type*} [Field k] [NumberField k]
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) ->
      NumberFieldFinitePlace.FinitePlaceQCandidate lowerPlace.val)
    (selected_nonempty : selectedLowerPlaces.Nonempty)
    (targetSigned thetaSigned : Real)
    (q_le_target :
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
        selectedLowerPlaces parameters <= targetSigned)
    (target_le_theta : targetSigned <= thetaSigned)
    (ipl she apt : Prop) (ipl_evidence : ipl)
    (she_evidence : she) (apt_evidence : apt) :
    (stepXIInputOfAbsoluteDegreeNormalizedSignedLog carrier input
      selectedLowerPlaces parameters selected_nonempty targetSigned thetaSigned
      q_le_target target_le_theta ipl she apt ipl_evidence she_evidence
      apt_evidence).qSigned =
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
        selectedLowerPlaces parameters := rfl

end ParametricStepXI

/-! ## 5. ArithmeticLink: the source wire is definitional; arithmetic fields are projections -/

namespace SourceProcessionStepXI

open MultiradialKernel ParametricStepXI

universe u v w

variable {l : PrimeGeFive} {V : Type v}
variable {Label : Type u} {Choice : Type w} [AddGroup Label]

variable (input : SourceProcessionBoundary.Input (l := l) (V := V)
  (Label := Label) (Choice := Choice))

/-- Any `StepXIInput` over the source-procession route has its output
definitionally equal to the wall output: the `output_is_run` field of
`StepXIInput` and the `output_is_run` field of the `StepXIWallCertificate` both
pin the value to `runAlgorithm`.  Hence the `arithmetic_source` field of
`ArithmeticLink` is derivable and not an independent source-facing input. -/
theorem arithmetic_output_eq_wall_theorem311
    (route : List (RouteStep Label))
    (arithmetic : StepXIInput input.carrier
      ((routeWall input route).routeOutput.algorithmInput)) :
    arithmetic.output = (routeWall input route).wall.theorem311 :=
  arithmetic.output_is_run.trans
    ((routeWall input route).wall.output_is_run).symm

/-- `ArithmeticLink` is constructible from its `StepXIInput` alone: the
`arithmetic_source` wire is definitional and the three arithmetic fields
(`q_negative`, `q_le_target`, `target_le_theta`) are projections of the input.
No wire hypothesis remains to be supplied. -/
def arithmeticLinkOfStepXIInput
    (route : List (RouteStep Label))
    (arithmetic : StepXIInput input.carrier
      ((routeWall input route).routeOutput.algorithmInput)) :
    ArithmeticLink input route where
  arithmetic := arithmetic
  arithmetic_source := arithmetic_output_eq_wall_theorem311 input route arithmetic
  q_negative := arithmetic.q_negative
  q_le_target := arithmetic.q_le_target
  target_le_theta := arithmetic.target_le_theta

@[simp] theorem arithmeticLinkOfStepXIInput_arithmetic
    (route : List (RouteStep Label))
    (arithmetic : StepXIInput input.carrier
      ((routeWall input route).routeOutput.algorithmInput)) :
    (arithmeticLinkOfStepXIInput input route arithmetic).arithmetic =
      arithmetic := rfl

/-- The composed source-procession link whose `StepXIInput` carries the actual
absolute-degree-normalized signed q-log and the algorithm output: the only
remaining fields are the two named real inequalities and the IPL/SHE/APT
evidence. -/
def arithmeticLinkOfAbsoluteDegreeNormalizedSignedLog
    (route : List (RouteStep Label))
    {k : Type*} [Field k] [NumberField k]
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) ->
      NumberFieldFinitePlace.FinitePlaceQCandidate lowerPlace.val)
    (selected_nonempty : selectedLowerPlaces.Nonempty)
    (targetSigned thetaSigned : Real)
    (q_le_target :
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
        selectedLowerPlaces parameters <= targetSigned)
    (target_le_theta : targetSigned <= thetaSigned)
    (ipl she apt : Prop) (ipl_evidence : ipl)
    (she_evidence : she) (apt_evidence : apt) :
    ArithmeticLink input route :=
  arithmeticLinkOfStepXIInput input route
    (stepXIInputOfAbsoluteDegreeNormalizedSignedLog input.carrier
      (routeWall input route).routeOutput.algorithmInput
      selectedLowerPlaces parameters selected_nonempty
      targetSigned thetaSigned q_le_target target_le_theta
      ipl she apt ipl_evidence she_evidence apt_evidence)

end SourceProcessionStepXI

end

end LeanFormal.IUT
