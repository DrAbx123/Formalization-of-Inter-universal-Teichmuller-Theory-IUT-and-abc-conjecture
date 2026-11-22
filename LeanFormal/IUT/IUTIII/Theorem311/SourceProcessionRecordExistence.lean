import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionBoundary
import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteMultiradial
import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteParameterized
import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteRouteArithmetic
import LeanFormal.IUT.Audit.Status
import Mathlib.Tactic

/-!
  Theorem 3.11-side source-procession record existence, reduced to two named
  inputs.

  The record type is `SourceProcessionBoundary.Input` (IUT III, Theorem 3.11,
  (i); the Q(i)-at-5 instance was constructed in `SourceProcessionBoundary`).
  This file proves that record existence at a fixed source Hodge theater
  together with a fixed parameterized carrier is equivalent to the two
  inputs:

  * `InputBridgeData.volume_bridge`: the carrier log-volume at the core base
    equals the theta-packet log-volume of the theater (IUT III, Theorem 3.11,
    (i), (a); procession-normalized mono-analytic log-volumes of
    Proposition 3.9, (ii), built on Proposition 3.2, (ii));
  * `InputBridgeData.route_normal_form`: every route started at the core base
    reaches an Ind3 iterate of a base-level choice (IUT III, Theorem 3.11,
    (i): the procession of D-prime-strips obtained by applying the natural
    functor of [IUTchI], Proposition 6.9, (ii)).

  Everything else in the record is discharged structurally: the base choice,
  the packet volume, the target q-parameter, and the q-consistency between
  the source and the terminal theta-packet, the latter for every dependent
  history via the proved theorem `HodgeTheaterHistory.composite_q`.

  The existence of the record for an arbitrary source Hodge theater carrying
  the paper's distinct-theater procession data remains open; this file does
  not claim it.  The equivalence below is the honest reduction: it names
  exactly which two source-facing conditions are missing.
-/

namespace LeanFormal.IUT

noncomputable section

namespace SourceProcessionBoundary

open HodgeTheaterHistory
open MultiradialKernel
open MultiradialKernel.Core
open ParametricTheorem311
open ParametricDStage

universe ua uv upi umon u w

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type u} {Choice : Type w} [AddGroup Label]

/- The two named inputs to which record existence at a fixed
   theater/carrier pair is reduced.  The universe parameters occur through
   the theater exactly as in `Input`; suppressing the universe-occurrence
   linter does not alter kernel checking or any proof term. -/
set_option linter.checkUnivs false in
structure InputBridgeData (T : HodgeTheater.{ua, uv, upi, umon} l V)
    (C : Carrier Label Choice) where
  volume_bridge : C.profile.logVolume C.core.base = T.thetaPacket.logVolume
  route_normal_form : ∀ (route : List (RouteStep Label)),
    ∃ b n,
      C.core.level b = C.core.level C.core.base ∧
      routeTarget C route C.core.base = C.core.ind3 n b

namespace Input

/- Assemble a record from a dependent history and the two bridge inputs.
   The base choice is the carrier core base, the packet volume is the
   carrier log-volume, and the q-consistency field is discharged by the
   proved history-composition theorem, for every dependent history. -/
set_option linter.checkUnivs false in
def ofBridgeData (T : HodgeTheater.{ua, uv, upi, umon} l V)
    (H : HodgeTheaterHistory.{ua, uv, upi, umon} l V T)
    (C : Carrier Label Choice)
    (bridge : InputBridgeData (l := l) (V := V) (Label := Label)
      (Choice := Choice) T C) :
    Input (l := l) (V := V) (Label := Label) (Choice := Choice) where
  theater := T
  history := H
  carrier := C
  baseChoice := C.core.base
  baseChoice_eq := rfl
  packetVolume := fun c => C.profile.logVolume c
  packetVolume_eq_profile := fun _ => rfl
  base_packetVolume_eq_theta := bridge.volume_bridge
  target_q := H.terminal.thetaPacket.q
  target_q_eq := rfl
  history_q_eq := HodgeTheaterHistory.composite_q H
  route_normal_form := bridge.route_normal_form

theorem ofBridgeData_theater (T : HodgeTheater.{ua, uv, upi, umon} l V)
    (H : HodgeTheaterHistory.{ua, uv, upi, umon} l V T)
    (C : Carrier Label Choice)
    (bridge : InputBridgeData (l := l) (V := V) (Label := Label)
      (Choice := Choice) T C) :
    (ofBridgeData T H C bridge).theater = T := rfl

theorem ofBridgeData_history (T : HodgeTheater.{ua, uv, upi, umon} l V)
    (H : HodgeTheaterHistory.{ua, uv, upi, umon} l V T)
    (C : Carrier Label Choice)
    (bridge : InputBridgeData (l := l) (V := V) (Label := Label)
      (Choice := Choice) T C) :
    (ofBridgeData T H C bridge).history = H := rfl

theorem ofBridgeData_carrier (T : HodgeTheater.{ua, uv, upi, umon} l V)
    (H : HodgeTheaterHistory.{ua, uv, upi, umon} l V T)
    (C : Carrier Label Choice)
    (bridge : InputBridgeData (l := l) (V := V) (Label := Label)
      (Choice := Choice) T C) :
    (ofBridgeData T H C bridge).carrier = C := rfl

theorem ofBridgeData_baseChoice (T : HodgeTheater.{ua, uv, upi, umon} l V)
    (H : HodgeTheaterHistory.{ua, uv, upi, umon} l V T)
    (C : Carrier Label Choice)
    (bridge : InputBridgeData (l := l) (V := V) (Label := Label)
      (Choice := Choice) T C) :
    (ofBridgeData T H C bridge).baseChoice = C.core.base := rfl

theorem ofBridgeData_target_q_eq_theta
    (T : HodgeTheater.{ua, uv, upi, umon} l V)
    (H : HodgeTheaterHistory.{ua, uv, upi, umon} l V T)
    (C : Carrier Label Choice)
    (bridge : InputBridgeData (l := l) (V := V) (Label := Label)
      (Choice := Choice) T C) :
    (ofBridgeData T H C bridge).target_q = T.thetaPacket.q :=
  (HodgeTheaterHistory.composite_q H).symm

set_option linter.defProp false in
def toBridgeData
    (input : Input (l := l) (V := V) (Label := Label) (Choice := Choice)) :
    InputBridgeData (l := l) (V := V) (Label := Label) (Choice := Choice)
      input.theater input.carrier where
  volume_bridge := input.profile_base_eq_theta
  route_normal_form := input.route_normal_form

theorem toBridgeData_ofBridgeData (T : HodgeTheater.{ua, uv, upi, umon} l V)
    (H : HodgeTheaterHistory.{ua, uv, upi, umon} l V T)
    (C : Carrier Label Choice)
    (bridge : InputBridgeData (l := l) (V := V) (Label := Label)
      (Choice := Choice) T C) :
    toBridgeData (ofBridgeData T H C bridge) = bridge :=
  Subsingleton.elim _ _

theorem record_exists_iff_bridgeData
    (T : HodgeTheater.{ua, uv, upi, umon} l V)
    (C : Carrier Label Choice) :
    (∃ input : Input (l := l) (V := V) (Label := Label) (Choice := Choice),
      input.theater = T ∧ input.carrier = C) ↔
      InputBridgeData (l := l) (V := V) (Label := Label) (Choice := Choice)
        T C := by
  constructor
  · rintro ⟨input, htheater, hcarrier⟩
    cases htheater
    cases hcarrier
    exact toBridgeData input
  · intro bridge
    exact ⟨ofBridgeData T (HodgeTheaterHistory.singleton T) C bridge,
      ofBridgeData_theater T (HodgeTheaterHistory.singleton T) C bridge,
      ofBridgeData_carrier T (HodgeTheaterHistory.singleton T) C bridge⟩

set_option linter.defProp false in
def concreteBridgeData (l : PrimeGeFive) :
    InputBridgeData (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      (T := ConcreteSourceHistoryLinkBridge.sourceTheater l)
      (C := SourceFiniteParameterized.carrier l) where
  volume_bridge := SourceFiniteMultiradial.emptyRouteOutput_log_volume l
  route_normal_form := by
    intro route
    refine ⟨ConcreteRouteNormalForm.horizontalTarget route
        ConcreteFiniteTheorem311.ProcessionChoice.base,
      ParametricTheorem311.verticalBudget route, ?_, ?_⟩
    · exact ConcreteRouteNormalForm.horizontalTarget_level route
        ConcreteFiniteTheorem311.ProcessionChoice.base
    · change SourceFiniteRouteArithmetic.target l route
          ConcreteFiniteTheorem311.ProcessionChoice.base =
        ConcreteFiniteTheorem311.ProcessionChoice.ind3Lift
          (ParametricTheorem311.verticalBudget route)
          (SourceFiniteRouteArithmetic.target l
            (ConcreteRouteNormalForm.horizontalPart route)
            ConcreteFiniteTheorem311.ProcessionChoice.base)
      exact ConcreteRouteNormalForm.normalized_target_eq route
        ConcreteFiniteTheorem311.ProcessionChoice.base

def concreteViaBridgeData (l : PrimeGeFive) :
    Input (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l) :=
  ofBridgeData (ConcreteSourceHistoryLinkBridge.sourceTheater l)
    (ConcreteSourceHistoryLinkBridge.sourceHistory l)
    (SourceFiniteParameterized.carrier l)
    (concreteBridgeData l)

theorem concreteViaBridgeData_theater (l : PrimeGeFive) :
    (concreteViaBridgeData l).theater =
      (concreteInput l).theater := rfl

theorem concreteViaBridgeData_history (l : PrimeGeFive) :
    (concreteViaBridgeData l).history =
      (concreteInput l).history := rfl

theorem concreteViaBridgeData_carrier (l : PrimeGeFive) :
    (concreteViaBridgeData l).carrier =
      (concreteInput l).carrier := rfl

theorem concreteRecord_via_reduction (l : PrimeGeFive) :
    ∃ input : Input (l := l) (V := FinitePrimePlace 2 7)
        (Label := ConcreteFiniteTheorem311.finiteLabel l)
        (Choice := ConcreteFiniteTheorem311.ProcessionChoice l),
      input.theater = ConcreteSourceHistoryLinkBridge.sourceTheater l ∧
      input.carrier = SourceFiniteParameterized.carrier l :=
  (record_exists_iff_bridgeData
    (l := l) (V := FinitePrimePlace 2 7)
    (Label := ConcreteFiniteTheorem311.finiteLabel l)
    (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
    (T := ConcreteSourceHistoryLinkBridge.sourceTheater l)
    (C := SourceFiniteParameterized.carrier l)).mpr (concreteBridgeData l)

theorem concreteBridgeData_eq_toBridgeData_concreteInput (l : PrimeGeFive) :
    concreteBridgeData l = toBridgeData (concreteInput l) :=
  Subsingleton.elim _ _

end Input

end SourceProcessionBoundary

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def sourceProcessionRecordExistence : Obligation :=
  { id := "IUT-III.source-procession-record-existence"
    source := "IUT III, Theorem 3.11, (i); source procession record input"
    status := VerificationStatus.conditional
    note :=
      "Record existence at a fixed source Hodge theater and parameterized " ++
        "carrier is proved equivalent to two named inputs: the base " ++
        "log-volume bridge and the route normal form of every base-started " ++
        "route (SourceProcessionBoundary.Input.record_exists_iff_bridgeData). " ++
        "The base choice, packet volume, target q-parameter, and the " ++
        "q-consistency of the source and terminal packets are discharged " ++
        "structurally; the q-consistency holds for every dependent history " ++
        "via HodgeTheaterHistory.composite_q. Both named inputs are proved " ++
        "for the Q(i)-at-5 instance, and the assembled record reproduces " ++
        "the frozen concreteInput components definitionally. The existence " ++
        "of the record for an arbitrary source Hodge theater carrying the " ++
        "paper's distinct-theater procession data remains open; this entry " ++
        "does not claim it."
    dependsOn :=
      [ "IUT-I.hodge-theater-history-composition",
        "IUT-III.parametric-D-stage-certificates",
        "IUT-III.concrete-route-normal-form" ] }

end LeanFormal.IUT.Audit
