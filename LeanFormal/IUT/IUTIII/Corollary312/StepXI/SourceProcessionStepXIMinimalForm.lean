import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceProcessionStepXI
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ContractSourceReduction
import Mathlib.Tactic

/-!
# Minimal comparison form of the Step-XI source-procession boundary

Downdrill record (2026-10-16) for the obligation
`IUT-III.source-procession-stepXI-boundary` (`SourceProcessionStepXI.lean:400`),
covering the two real comparison fields `q_le_target` / `target_le_theta` of
`SourceProcessionStepXI.ArithmeticLink`.

Corpus anchors (IUT III, Corollary 3.12 proof, Step (xi)):

* (xi-d): `R^{<= -|log(Theta)|} := {lambda in R | lambda <= -|log(Theta)|}
  subset R; -|log(q)| in R`, where `-|log(Theta)|` is by definition the
  log-volume of the holomorphic hull `1,circ U` and `-|log(q)|` is the
  q-pilot log-volume of the input data.
* (xi-f): `-|log(q)| in R^{<= -|log(Theta)|}`, hence
  `-|log(q)| <= -|log(Theta)| in R`, i.e. `C_Theta >= -1`.

The corpus comparison is two-term; the middle element `targetSigned` is the
repo's hull anchor.  This file records, with proofs:

* `comparisonChain_iff_single`: the two-field chain `q <= t <= theta` has
  exactly the ordered content of the single comparison `q <= theta`
  (middle elimination; the middle is free for the ordered conclusion).
* `stepXIContract_exists_of_singleComparison` and
  `singleComparison_of_stepXIContract`: the contract surface is inhabited as
  soon as `q < 0` and `q <= theta` (the middle may be chosen at an endpoint);
  conversely any contract yields the single comparison.
* `stepXIComparisonData_*`: on the scalar data surface the two comparisons and
  the negativity are independent constraints -- each is falsifiable while the
  rest remain satisfiable.  The explicit comparison fields therefore cannot be
  dropped or re-derived from the remaining field data; any closure has to
  supply the arithmetic content itself.
* `arithmeticLinkOfHullInclusion` and
  `arithmeticLinkOfHullInclusionOfAbsoluteDegreeNormalizedSignedLog`: the
  hull-pinned source-procession link.  From the single (xi-f)-shaped inclusion
  `q <= hullValue` (with q either free or the actual compiled
  absolute-degree-normalized signed q-log) and the pinning
  `target = theta = hullValue`, the `ArithmeticLink` surface is constructed;
  the second comparison is `le_rfl`.

The V1 two-field surface remains unchanged; the V2 pinned mirror lives in
`SourceProcessionStepXI.lean` (section "V2 pinned comparison form").  No
source-facing existence is manufactured: the residual named input of this file
is the single (xi-f) inclusion `q <= hullValue` at a supplied hull value (the
Card-HULLREAL supply face), together with the IPL/SHE/APT evidence.
-/

namespace LeanFormal.IUT

noncomputable section

namespace SourceStepXIComparisonForm

/-- Middle elimination: a two-step real chain `q <= target <= theta` exists
exactly when the single comparison `q <= theta` holds.  The middle element
adds no strength to the ordered conclusion; it carries the hull anchor. -/
theorem comparisonChain_iff_single (q theta : Real) :
    (∃ target : Real, q ≤ target ∧ target ≤ theta) ↔ q ≤ theta := by
  constructor
  · rintro ⟨target, hq, ht⟩
    exact le_trans hq ht
  · intro h
    exact ⟨q, le_rfl, h⟩

/-- The contract surface is inhabited from the single comparison: with
`q < 0` and `q <= theta`, a contract exists whose middle element is the lower
endpoint, so `q_le_target` holds by `le_rfl`. -/
theorem stepXIContract_exists_of_singleComparison (q theta : Real) (hq : q < 0)
    (h : q ≤ theta) (ipl she apt : Prop) (ipl_evidence : ipl)
    (she_evidence : she) (apt_evidence : apt) :
    ∃ contract : StepXIContract,
      contract.qSigned = q ∧ contract.thetaSigned = theta ∧
        contract.targetSigned = q ∧ Cor312Conclusion contract :=
  ⟨{ qSigned := q
     thetaSigned := theta
     targetSigned := q
     q_negative := hq
     ipl := ipl
     she := she
     apt := apt
     ipl_evidence := ipl_evidence
     she_evidence := she_evidence
     apt_evidence := apt_evidence
     q_le_target := le_rfl
     target_le_theta := h },
   rfl, rfl, rfl, h⟩

/-- Conversely, any contract yields the single comparison; this is the
existing `cor312_of_constructed_stepXI` in shape form. -/
theorem singleComparison_of_stepXIContract (contract : StepXIContract) :
    contract.qSigned ≤ contract.thetaSigned :=
  cor312_of_constructed_stepXI contract

/-- Scalar data surface of the two comparison fields: the arithmetic scalars
with the negativity constraint, without the two comparison proofs.  It is used
only to record that the comparisons are independent constraints on this
surface. -/
structure StepXIComparisonData where
  qSigned : Real
  targetSigned : Real
  thetaSigned : Real
  q_negative : qSigned < 0

/-- The comparison `q <= target` is not implied by the remaining data: it is
falsifiable with the negativity constraint satisfied. -/
theorem stepXIComparisonData_q_le_target_independent :
    ∃ d : StepXIComparisonData, ¬ d.qSigned ≤ d.targetSigned :=
  ⟨{ qSigned := -1, targetSigned := -2, thetaSigned := -1,
     q_negative := by norm_num },
   by norm_num⟩

/-- The comparison `target <= theta` is not implied by the other comparison or
by the negativity constraint: it is falsifiable while the first comparison
holds. -/
theorem stepXIComparisonData_target_le_theta_independent :
    ∃ d : StepXIComparisonData,
      d.qSigned ≤ d.targetSigned ∧ ¬ d.targetSigned ≤ d.thetaSigned :=
  ⟨{ qSigned := -2, targetSigned := -1, thetaSigned := -2,
     q_negative := by norm_num },
   by norm_num, by norm_num⟩

/-- Both comparisons together are satisfiable with the negativity constraint
(so no comparison is refuted on the data surface, either). -/
theorem stepXIComparisonData_satisfiable :
    ∃ d : StepXIComparisonData,
      d.qSigned ≤ d.targetSigned ∧ d.targetSigned ≤ d.thetaSigned :=
  ⟨{ qSigned := -2, targetSigned := -1, thetaSigned := 0,
     q_negative := by norm_num },
   by norm_num, by norm_num⟩

/-- The negativity constraint is not implied by the two comparisons. -/
theorem stepXIComparisonData_negativity_independent :
    ∃ q target theta : Real, q ≤ target ∧ target ≤ theta ∧ ¬ q < 0 :=
  ⟨0, 0, 0, le_rfl, le_rfl, by norm_num⟩

end SourceStepXIComparisonForm

open SourceProcessionBoundary
open MultiradialKernel
open MultiradialKernel.Core
open ParametricTheorem311
open ParametricDStage
open ParametricStepXI

namespace SourceProcessionStepXI

universe u v w

variable {l : PrimeGeFive} {V : Type v}
variable {Label : Type u} {Choice : Type w} [AddGroup Label]

variable (input : SourceProcessionBoundary.Input (l := l) (V := V)
  (Label := Label) (Choice := Choice))

/-- Hull-pinned arithmetic link at the V1 surface: one named real inclusion
`q <= hullValue` (the (xi-f) content) with `target = theta = hullValue`; the
second comparison is definitional (`le_rfl`) and the `arithmetic_source` wire is
discharged by `ContractSourceReduction.arithmeticLinkOfStepXIInput`. -/
def arithmeticLinkOfHullInclusion (route : List (RouteStep Label))
    (qSigned hullValue : Real) (hq : qSigned < 0) (q_le_hull : qSigned ≤ hullValue)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :
    ArithmeticLink input route :=
  arithmeticLinkOfStepXIInput input route
    (stepXIInput input.carrier (routeWall input route).routeOutput.algorithmInput
      qSigned hullValue hullValue hq ipl she apt
      ipl_evidence she_evidence apt_evidence q_le_hull le_rfl)

@[simp] theorem arithmeticLinkOfHullInclusion_qSigned
    (route : List (RouteStep Label))
    (qSigned hullValue : Real) (hq : qSigned < 0) (q_le_hull : qSigned ≤ hullValue)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :
    (arithmeticLinkOfHullInclusion input route qSigned hullValue hq q_le_hull
      ipl she apt ipl_evidence she_evidence apt_evidence).arithmetic.qSigned =
      qSigned := rfl

@[simp] theorem arithmeticLinkOfHullInclusion_targetSigned
    (route : List (RouteStep Label))
    (qSigned hullValue : Real) (hq : qSigned < 0) (q_le_hull : qSigned ≤ hullValue)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :
    (arithmeticLinkOfHullInclusion input route qSigned hullValue hq q_le_hull
      ipl she apt ipl_evidence she_evidence apt_evidence).arithmetic.targetSigned =
      hullValue := rfl

@[simp] theorem arithmeticLinkOfHullInclusion_thetaSigned
    (route : List (RouteStep Label))
    (qSigned hullValue : Real) (hq : qSigned < 0) (q_le_hull : qSigned ≤ hullValue)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :
    (arithmeticLinkOfHullInclusion input route qSigned hullValue hq q_le_hull
      ipl she apt ipl_evidence she_evidence apt_evidence).arithmetic.thetaSigned =
      hullValue := rfl

/-- Under the pinning the second comparison is definitional: `target` and
`theta` are the same term. -/
theorem arithmeticLinkOfHullInclusion_target_eq_theta
    (route : List (RouteStep Label))
    (qSigned hullValue : Real) (hq : qSigned < 0) (q_le_hull : qSigned ≤ hullValue)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :
    (arithmeticLinkOfHullInclusion input route qSigned hullValue hq q_le_hull
      ipl she apt ipl_evidence she_evidence apt_evidence).arithmetic.targetSigned =
      (arithmeticLinkOfHullInclusion input route qSigned hullValue hq q_le_hull
        ipl she apt ipl_evidence she_evidence apt_evidence).arithmetic.thetaSigned :=
  rfl

/-- The single remaining arithmetic input of the pinned link is exactly the
(xi-f) inclusion `q <= target`. -/
theorem arithmeticLinkOfHullInclusion_singleInclusion
    (route : List (RouteStep Label))
    (qSigned hullValue : Real) (hq : qSigned < 0) (q_le_hull : qSigned ≤ hullValue)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :
    (arithmeticLinkOfHullInclusion input route qSigned hullValue hq q_le_hull
      ipl she apt ipl_evidence she_evidence apt_evidence).arithmetic.qSigned ≤
      (arithmeticLinkOfHullInclusion input route qSigned hullValue hq q_le_hull
        ipl she apt ipl_evidence she_evidence apt_evidence).arithmetic.targetSigned :=
  q_le_hull

/-- The corpus conclusion at the pinned link: `q <= theta`, i.e. `C_Theta >= -1`
in the shape of (xi-f). -/
theorem arithmeticLinkOfHullInclusion_conclusion
    (route : List (RouteStep Label))
    (qSigned hullValue : Real) (hq : qSigned < 0) (q_le_hull : qSigned ≤ hullValue)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :
    Cor312Conclusion
      ((arithmeticLinkOfHullInclusion input route qSigned hullValue hq q_le_hull
        ipl she apt ipl_evidence she_evidence apt_evidence).arithmetic.toContract) :=
  (arithmeticLinkOfHullInclusion input route qSigned hullValue hq q_le_hull
    ipl she apt ipl_evidence she_evidence apt_evidence).arithmetic.conclusion

/-- The hull-pinned link with the scalar instantiated by the actual
absolute-degree-normalized signed q-log of a finite-place q-family
(`ArithmeticQPilotGlobalNormalization`); the negativity is proved from the
nonempty selection, so the single named input is the inclusion
`q <= hullValue`. -/
def arithmeticLinkOfHullInclusionOfAbsoluteDegreeNormalizedSignedLog
    (route : List (RouteStep Label))
    {k : Type*} [Field k] [NumberField k]
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) ->
      NumberFieldFinitePlace.FinitePlaceQCandidate lowerPlace.val)
    (selected_nonempty : selectedLowerPlaces.Nonempty)
    (hullValue : Real)
    (q_le_hull :
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
        selectedLowerPlaces parameters ≤ hullValue)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :
    ArithmeticLink input route :=
  arithmeticLinkOfHullInclusion input route
    (ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
      selectedLowerPlaces parameters)
    hullValue
    (ArithmeticQPilotGlobalNormalization.normalizedLowerSignedLog_neg
      selectedLowerPlaces parameters selected_nonempty)
    q_le_hull ipl she apt ipl_evidence she_evidence apt_evidence

@[simp] theorem arithmeticLinkOfHullInclusionOfAbsoluteDegreeNormalizedSignedLog_qSigned
    (route : List (RouteStep Label))
    {k : Type*} [Field k] [NumberField k]
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) ->
      NumberFieldFinitePlace.FinitePlaceQCandidate lowerPlace.val)
    (selected_nonempty : selectedLowerPlaces.Nonempty)
    (hullValue : Real)
    (q_le_hull :
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
        selectedLowerPlaces parameters ≤ hullValue)
    (ipl she apt : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (apt_evidence : apt) :
    (arithmeticLinkOfHullInclusionOfAbsoluteDegreeNormalizedSignedLog input route
      selectedLowerPlaces parameters selected_nonempty hullValue q_le_hull
      ipl she apt ipl_evidence she_evidence apt_evidence).arithmetic.qSigned =
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
        selectedLowerPlaces parameters := rfl

end SourceProcessionStepXI

end

end LeanFormal.IUT
