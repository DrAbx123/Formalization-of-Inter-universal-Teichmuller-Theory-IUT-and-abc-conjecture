import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ContractSourceReduction
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ParametricStepXI
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotGlobalNormalization
import LeanFormal.IUT.Audit.Status
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Card-QCMP conditional assembly: the source-level real comparison `q <= target <= theta`

This module solidifies the Card-QCMP conditional assembly path of the Step-XI
north wall (report `logs/coordination/stepxi-contract-reduction-20261016.md`,
section "Card-QCMP" and observation O1), with the same shape as the landed
Card-IPL upgrade (`IUTIII/Theorem311/SourcePolyIsoTransportLaws.lean`): a
named supply structure with the obligation fields as hypotheses, reduction
laws conditional on the supply, canonical collapse points, and alignment with
the consumer's comparison fields.

## Fixed here

1. `QCMPComparisonSupply` -- the left end of the comparison is the
   object-level named quantity
   `ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog`
   of an actual finite-place q-family, and the two hypothesis fields are the
   two comparison faces `q <= target` and `target <= theta`.  The repository
   has no object-level definition of `target`; the field carries that
   obligation.
2. Reduction laws: the ordered form `QCMPComparisonSupply.q_le_theta` (the
   Cor 3.12 conclusion face), the horizon form `exists_target_between_iff`,
   and the canonical collapse points `ofCanonicalCollapse` and
   `ofTargetEqLowerSignedLog`.
3. Consumer alignment: `QCMPComparisonSupply.toStepXIContract` feeds the
   `StepXIContract` fields `q_le_target` and `target_le_theta`
   definitionally, with projection lemmas recording that the consumed fields
   are the supply's own fields; `cor312Conclusion_of_toStepXIContract`
   reaches the ordered conclusion through the existing consumer theorem.
   The parametric `StepXIInput` path is wired the same way
   (`toStepXIInput`).

## Paper anchors

* IUT III, Corollary 3.12, proof, Step (xi): the source-level comparison
  `q <= target`; Steps (xi-d)--(xi-g): the amplitude relations used to reach
  the target comparison.
* IUT III, Remark 3.9.5 (weighted determinant normalization), consumed by the
  target/theta scale.

## Frozen obstacles recorded, not bypassed

* The repository's q family reaches only the arithmetic normalization
  invariants; `ArithmeticQPilotGlobalNormalization` itself records that the
  identification with the paper's global q-pilot (Tate uniformization,
  coricity, theta-hull properties) is not established here.
* The target has no object-level definition in the repository.
* On the value layer, the lower bound exists only in `ENNReal` form and needs
  `hdeg`; the real-layer transfer combined with finiteness has empty premise
  space (report O1: `sourceHullVolume_eq_top_of_degreeFaithful` forces
  `sourceHullVolume = top` under `hdeg`).  No field of the supply is
  therefore discharged here from value-layer data.

Nothing below constructs a source instantiation of the supply, and no
existing statement is weakened.  The theta face carried by `target_le_theta`
is the same face consumed by the certificate/hull route (`target` taken as
the hull volume, field `hull_le_theta`); its source discharge is the
registered certificate-hull/AMPL boundary and is not re-proved here.
-/

namespace LeanFormal.IUT

noncomputable section

namespace StepXIQCMP

variable {k : Type*} [Field k] [NumberField k]

/-- The Card-QCMP named supply: an actual finite-place q-family with its
nonemptiness, the object-level signed q-log quantity
`absoluteDegreeNormalizedLowerSignedLog selectedLowerPlaces parameters` as the
left end, and the two comparison faces as fields.  The fields are discharge
obligations; no source instantiation is constructed or asserted, and no
object-level definition of `targetSigned` is claimed to exist. -/
structure QCMPComparisonSupply (k : Type*) [Field k] [NumberField k] where
  selectedLowerPlaces : Finset (NumberField.FinitePlace k)
  parameters : (lowerPlace : selectedLowerPlaces) ->
    NumberFieldFinitePlace.FinitePlaceQCandidate lowerPlace.val
  selected_nonempty : selectedLowerPlaces.Nonempty
  targetSigned : Real
  thetaSigned : Real
  q_le_target :
    ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
      selectedLowerPlaces parameters ≤ targetSigned
  target_le_theta : targetSigned ≤ thetaSigned

/-- Ordered form: a supply proves the Cor 3.12 ordered comparison between the
named signed q-log quantity and the theta scale. -/
theorem QCMPComparisonSupply.q_le_theta (S : QCMPComparisonSupply k) :
    ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
      S.selectedLowerPlaces S.parameters ≤ S.thetaSigned :=
  le_trans S.q_le_target S.target_le_theta

/-- Horizon form: for an unconstrained real target, the existence of the
comparison pair `q <= target <= theta` is equivalent to the endpoint
comparison `q <= theta`.  This isolates the honest content of Card-QCMP: the
left-end source instantiation together with a source-meaningful target, not
the bare existence of an ordered pair. -/
theorem exists_target_between_iff {q theta : Real} :
    (∃ target : Real, q ≤ target ∧ target ≤ theta) ↔ q ≤ theta := by
  constructor
  · rintro ⟨target, h1, h2⟩
    exact le_trans h1 h2
  · intro h
    exact ⟨q, le_rfl, h⟩

/-- Canonical collapse at the degenerate point `target = theta = q`: the
supply shape is satisfiable over any actual finite-place q-family with a
nonempty selection, with no horizon input.  This is a canonical field-level
witness of the frozen shape, not a source instantiation. -/
def QCMPComparisonSupply.ofCanonicalCollapse
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) ->
      NumberFieldFinitePlace.FinitePlaceQCandidate lowerPlace.val)
    (selected_nonempty : selectedLowerPlaces.Nonempty) :
    QCMPComparisonSupply k where
  selectedLowerPlaces := selectedLowerPlaces
  parameters := parameters
  selected_nonempty := selected_nonempty
  targetSigned :=
    ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
      selectedLowerPlaces parameters
  thetaSigned :=
    ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
      selectedLowerPlaces parameters
  q_le_target := le_rfl
  target_le_theta := le_rfl

/-- Canonical collapse with the target equal to the q-log quantity, under the
horizon input `theta >= q`: the pair `q <= target <= theta` then reduces to
the single horizon inequality.  Conditional form; the horizon inequality
against a source target is the Card-AMPL-side face and is not asserted
here. -/
def QCMPComparisonSupply.ofTargetEqLowerSignedLog
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) ->
      NumberFieldFinitePlace.FinitePlaceQCandidate lowerPlace.val)
    (selected_nonempty : selectedLowerPlaces.Nonempty)
    (thetaSigned : Real)
    (horizon :
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
        selectedLowerPlaces parameters ≤ thetaSigned) :
    QCMPComparisonSupply k where
  selectedLowerPlaces := selectedLowerPlaces
  parameters := parameters
  selected_nonempty := selected_nonempty
  targetSigned :=
    ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
      selectedLowerPlaces parameters
  thetaSigned := thetaSigned
  q_le_target := le_rfl
  target_le_theta := horizon

/-- The `StepXIContract` constructed from a supply plus the IPL/SHE/APT data;
the two comparison fields consumed by the contract are the supply's own
comparison faces. -/
def QCMPComparisonSupply.toStepXIContract (S : QCMPComparisonSupply k)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) : StepXIContract :=
  StepXIContract.ofAbsoluteDegreeNormalizedSignedLog
    S.selectedLowerPlaces S.parameters S.selected_nonempty
    S.targetSigned S.thetaSigned S.q_le_target S.target_le_theta
    ipl she apt ipl_evidence she_evidence apt_evidence

@[simp] theorem QCMPComparisonSupply.toStepXIContract_qSigned
    (S : QCMPComparisonSupply k) (ipl she apt : Prop) (ipl_evidence : ipl)
    (she_evidence : she) (apt_evidence : apt) :
    (S.toStepXIContract ipl she apt ipl_evidence she_evidence
      apt_evidence).qSigned =
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
        S.selectedLowerPlaces S.parameters := rfl

@[simp] theorem QCMPComparisonSupply.toStepXIContract_q_le_target
    (S : QCMPComparisonSupply k) (ipl she apt : Prop) (ipl_evidence : ipl)
    (she_evidence : she) (apt_evidence : apt) :
    (S.toStepXIContract ipl she apt ipl_evidence she_evidence
      apt_evidence).q_le_target = S.q_le_target := rfl

@[simp] theorem QCMPComparisonSupply.toStepXIContract_target_le_theta
    (S : QCMPComparisonSupply k) (ipl she apt : Prop) (ipl_evidence : ipl)
    (she_evidence : she) (apt_evidence : apt) :
    (S.toStepXIContract ipl she apt ipl_evidence she_evidence
      apt_evidence).target_le_theta = S.target_le_theta := rfl

/-- Consumer form: the ordered Cor 3.12 conclusion for the supply-backed
contract. -/
theorem cor312Conclusion_of_toStepXIContract (S : QCMPComparisonSupply k)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :
    Cor312Conclusion
      (S.toStepXIContract ipl she apt ipl_evidence she_evidence
        apt_evidence) :=
  cor312_of_constructed_stepXI _

/-! ## Parametric `StepXIInput` consumer alignment -/

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label]

/-- The parametric `StepXIInput` of the Step-XI assembly, built from the
supply and the Theorem 3.11 carrier/input data. -/
def QCMPComparisonSupply.toStepXIInput (S : QCMPComparisonSupply k)
    (carrier : ParametricTheorem311.Carrier Label Choice)
    (input : ParametricTheorem311.AlgorithmInput carrier)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :
    ParametricStepXI.StepXIInput carrier input :=
  ParametricStepXI.stepXIInputOfAbsoluteDegreeNormalizedSignedLog
    carrier input S.selectedLowerPlaces S.parameters S.selected_nonempty
    S.targetSigned S.thetaSigned S.q_le_target S.target_le_theta
    ipl she apt ipl_evidence she_evidence apt_evidence

@[simp] theorem QCMPComparisonSupply.toStepXIInput_q_le_target
    (S : QCMPComparisonSupply k)
    (carrier : ParametricTheorem311.Carrier Label Choice)
    (input : ParametricTheorem311.AlgorithmInput carrier)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :
    (S.toStepXIInput carrier input ipl she apt ipl_evidence she_evidence
      apt_evidence).q_le_target = S.q_le_target := rfl

@[simp] theorem QCMPComparisonSupply.toStepXIInput_toContract_q_le_target
    (S : QCMPComparisonSupply k)
    (carrier : ParametricTheorem311.Carrier Label Choice)
    (input : ParametricTheorem311.AlgorithmInput carrier)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :
    ((S.toStepXIInput carrier input ipl she apt ipl_evidence she_evidence
      apt_evidence).toContract).q_le_target = S.q_le_target := rfl

end StepXIQCMP

namespace Audit

/-- The Card-QCMP conditional assembly path: the named supply, the
conditional reduction laws, and the canonical collapse points, with the
source instantiation of the comparison left as the named card. -/
def cardQCMPComparisonSupply : Obligation :=
  { id := "IUT-III.card-qcmp-comparison-supply"
    source :=
      "IUT III, Corollary 3.12, proof, Step (xi) and Steps (xi-d)--(xi-g); " ++
        "Remark 3.9.5"
    status := VerificationStatus.interface
    note :=
      "Card-QCMP conditional assembly at the interface level: the named " ++
        "supply `QCMPComparisonSupply` (finite-place q-family with " ++
        "nonemptiness; left end = the object-level signed q-log " ++
        "`absoluteDegreeNormalizedLowerSignedLog`; comparison fields " ++
        "`q_le_target` and `target_le_theta`), the ordered law " ++
        "`QCMPComparisonSupply.q_le_theta`, the horizon form " ++
        "`exists_target_between_iff`, and the canonical collapse points " ++
        "`ofCanonicalCollapse` / `ofTargetEqLowerSignedLog`.  The " ++
        "`StepXIContract` and parametric `StepXIInput` consumers receive " ++
        "the supply's own comparison fields definitionally (projection " ++
        "lemmas).  Open: the source instantiation of `q_le_target` -- the " ++
        "identification of the repository q family with the paper's " ++
        "global q-pilot is NOT asserted, no object-level definition of " ++
        "the target exists in the repository, and the value-layer route " ++
        "is empty by report O1.  The theta face is the registered " ++
        "certificate-hull/AMPL boundary and is not re-proved here."
    dependsOn :=
      [ "IUT-III.StepXI.contract-construction",
        "IUT-III.corollary-3.12-step-XI-certificate-hull-wiring" ] }

/-- The Card-QCMP canonical collapse assessment: the frozen supply shape is
non-vacuous over an actual finite-place q-family. -/
def cardQCMPComparisonCanonicalCollapse : Obligation :=
  { id := "IUT-III.card-qcmp-comparison-canonical-collapse"
    source :=
      "IUT III, Corollary 3.12, proof, Step (xi); Remark 3.9.5"
    status := VerificationStatus.provedKernel
    note :=
      "Field-level satisfiability assessment of `QCMPComparisonSupply`: " ++
        "the canonical collapse points witness non-vacuity of the supply " ++
        "shape over an actual finite-place q-family (degenerate point " ++
        "`target = theta = q` unconditionally given a nonempty selection; " ++
        "`target = q` under the horizon input `theta >= q`), and the " ++
        "existence form is equivalent to the endpoint comparison for an " ++
        "unconstrained real target.  This is a canonical field-level " ++
        "witness, not a source instantiation of the target."
    dependsOn := [ "IUT-III.card-qcmp-comparison-supply" ] }

end Audit

end

end LeanFormal.IUT
