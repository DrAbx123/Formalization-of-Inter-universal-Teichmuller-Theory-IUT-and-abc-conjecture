import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionRecordExistence
import LeanFormal.IUT.IUTI.HodgeTheater.LinkVolumeTransport
import Mathlib.Tactic

/-!
  Theorem 3.11-side source-procession record existence: the two named inputs
  of `SourceProcessionBoundary.Input.record_exists_iff_bridgeData` are pushed
  from the Q(i)-at-5 instance towards an arbitrary source.

  The frozen equivalence reduced record existence at a fixed theater/carrier
  pair to the two conditions

  * `volume_bridge`: the carrier log-volume at the core base equals the
    theater's theta-packet log-volume (IUT III, Theorem 3.11, (i), (a);
    procession-normalized mono-analytic log-volumes of Proposition 3.9, (ii));
  * `route_normal_form`: every route started at the core base reaches an
    Ind3 iterate of a base-level choice (IUT III, Theorem 3.11, (i): the
    procession obtained by the natural functor of [IUTchI], Proposition
    6.9, (ii); corpus `Inter-universal Teichmuller Theory I.txt`:9811).

  This file advances both cards beyond the concrete instance:

  * the route normal form is proved for every `Carrier` (every label group,
    every choice type, every route): the horizontal/vertical split of a
    route, followed by the commutation of horizontal steps with Ind3,
    normalizes any route target.  The card is closed at this generality.
  * the volume bridge is *not* provable for every carrier: on a fixed
    theater, two constant carriers with different log-volumes give
    `0 = 1` (a precise negative result, with no analysis of theta zeros).
    What is proved instead: the bridge transports along Hodge-theater
    links and dependent histories (the log-volume analogue of the use of
    vertical coricity in Theorem 3.11, (i)); for every theater a
    compatible carrier exists; and the Q(i)-at-5 bridge is recovered from
    the frozen instance.

  Consequently record existence at a fixed theater/carrier pair is
  equivalent to the *single* named condition `VolumeBridge`.  The existence
  of the record for an arbitrary source Hodge theater carrying the paper's
  distinct-theater procession data remains open, exactly as recorded in
  `SourceProcessionRecordExistence.lean`: the remaining gap is the
  compatibility of the paper's carrier with the theater, which is a source
  input and is not claimed here.
-/

namespace LeanFormal.IUT

noncomputable section

namespace SourceProcessionBoundary

open HodgeTheaterHistory
open MultiradialKernel
open MultiradialKernel.Core
open ParametricTheorem311

universe ua uv upi umon u w

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type u} {Choice : Type w} [AddGroup Label]

/-! ## Card 2: route normal form, for an arbitrary carrier -/

/-- The horizontal part of a route: Ind1/Ind2 steps are kept, Ind3 steps are
    dropped.  This is the generic counterpart of
    `ConcreteRouteNormalForm.horizontalPart`, with no constraint on the
    label group. -/
def horizontalSteps : List (RouteStep Label) → List (RouteStep Label)
  | [] => []
  | .ind1 g :: rest => .ind1 g :: horizontalSteps rest
  | .ind2 g :: rest => .ind2 g :: horizontalSteps rest
  | .ind3 _ :: rest => horizontalSteps rest

omit [AddGroup Label] in
theorem verticalBudget_horizontalSteps (route : List (RouteStep Label)) :
    verticalBudget (horizontalSteps route) = 0 := by
  induction route with
  | nil => rfl
  | cons step rest ih =>
      cases step <;> simp [horizontalSteps, ih]

/-- An Ind3 step commutes with any single step, up to the Ind3 addition
    convention `ind3 (m + n) c = ind3 n (ind3 m c)`. -/
theorem applyStep_ind3_commute (core : Core Label Choice)
    (step : RouteStep Label) (m : Nat) (c : Choice) :
    applyStep core step (core.ind3 m c) =
      core.ind3 m (applyStep core step c) := by
  cases step with
  | ind1 g => exact core.ind1_ind3_commute g m c
  | ind2 g => exact core.ind2_ind3_commute g m c
  | ind3 n =>
      change core.ind3 n (core.ind3 m c) = core.ind3 m (core.ind3 n c)
      rw [← core.ind3_add m n c, Nat.add_comm m n, core.ind3_add n m c]

/-- The Ind3 action commutes with applying any route. -/
theorem routeTarget_ind3_commute (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (m : Nat) (c : Choice) :
    routeTarget carrier route (carrier.core.ind3 m c) =
      carrier.core.ind3 m (routeTarget carrier route c) := by
  induction route generalizing c with
  | nil => simp
  | cons step rest ih =>
      simp only [routeTarget_cons]
      rw [applyStep_ind3_commute carrier.core step m c]
      exact ih (applyStep carrier.core step c)

/-- The normal form: dropping the Ind3 steps from a route and applying them
    in one final Ind3 iterate reproduces the route target. -/
theorem routeTarget_normalize (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice) :
    routeTarget carrier route c =
      carrier.core.ind3 (verticalBudget route)
        (routeTarget carrier (horizontalSteps route) c) := by
  induction route generalizing c with
  | nil =>
      simpa [horizontalSteps] using (carrier.core.ind3_zero c).symm
  | cons step rest ih =>
      cases step with
      | ind1 g =>
          simp only [routeTarget_cons, applyStep_ind1, verticalBudget_ind1,
            horizontalSteps]
          exact ih (carrier.core.ind1 g c)
      | ind2 g =>
          simp only [routeTarget_cons, applyStep_ind2, verticalBudget_ind2,
            horizontalSteps]
          exact ih (carrier.core.ind2 g c)
      | ind3 n =>
          simp only [routeTarget_cons, applyStep_ind3, verticalBudget_ind3,
            horizontalSteps]
          rw [ih (carrier.core.ind3 n c),
            routeTarget_ind3_commute carrier (horizontalSteps rest) n c]
          exact (carrier.core.ind3_add n (verticalBudget rest)
            (routeTarget carrier (horizontalSteps rest) c)).symm

/-- Every route target is an Ind3 iterate of a choice at the level of the
    route's start. -/
theorem routeTarget_ind3_normal_form (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice) :
    ∃ b n, carrier.core.level b = carrier.core.level c ∧
      routeTarget carrier route c = carrier.core.ind3 n b := by
  refine ⟨routeTarget carrier (horizontalSteps route) c,
    verticalBudget route, ?_, ?_⟩
  · rw [routeTarget_level_eq_budget, verticalBudget_horizontalSteps,
      Nat.add_zero]
  · exact routeTarget_normalize carrier route c

/-- The frozen `InputBridgeData.route_normal_form` condition holds at every
    carrier, with the core base as the starting choice: the second named
    input of the boundary record is discharged generically, so only the
    log-volume bridge remains. -/
theorem route_normal_form_holds (carrier : Carrier Label Choice) :
    ∀ route : List (RouteStep Label),
      ∃ b n,
        carrier.core.level b = carrier.core.level carrier.core.base ∧
        routeTarget carrier route carrier.core.base =
          carrier.core.ind3 n b := by
  intro route
  exact routeTarget_ind3_normal_form carrier route carrier.core.base

/-! ## Card 1: the log-volume bridge -/

/- The single named input remaining after the route normal form is
    discharged: the carrier log-volume at the core base equals the theater's
    theta-packet log-volume (IUT III, Theorem 3.11, (i), (a)). -/
set_option linter.checkUnivs false in
structure VolumeBridge (T : HodgeTheater.{ua, uv, upi, umon} l V)
    (C : Carrier Label Choice) where
  volume_bridge : C.profile.logVolume C.core.base = T.thetaPacket.logVolume

set_option linter.checkUnivs false in
theorem inputBridgeData_iff_volumeBridge
    (T : HodgeTheater.{ua, uv, upi, umon} l V) (C : Carrier Label Choice) :
    InputBridgeData (l := l) (V := V) (Label := Label) (Choice := Choice)
        T C ↔
      VolumeBridge (l := l) (V := V) (Label := Label) (Choice := Choice)
        T C := by
  constructor
  · intro bridge
    exact ⟨bridge.volume_bridge⟩
  · intro bridge
    exact ⟨bridge.volume_bridge, route_normal_form_holds C⟩

set_option linter.checkUnivs false in
theorem record_exists_iff_volumeBridge
    (T : HodgeTheater.{ua, uv, upi, umon} l V) (C : Carrier Label Choice) :
    (∃ input : Input (l := l) (V := V) (Label := Label) (Choice := Choice),
      input.theater = T ∧ input.carrier = C) ↔
      VolumeBridge (l := l) (V := V) (Label := Label) (Choice := Choice)
        T C :=
  (Input.record_exists_iff_bridgeData (l := l) (V := V) (Label := Label)
      (Choice := Choice) (T := T) (C := C)).trans
    (inputBridgeData_iff_volumeBridge (T := T) (C := C))

set_option linter.checkUnivs false in
theorem volumeBridge_of_link {T T' : HodgeTheater.{ua, uv, upi, umon} l V}
    (C : Carrier Label Choice) (link : HodgeTheaterLink T' T)
    (bridge : VolumeBridge (l := l) (V := V) (Label := Label)
      (Choice := Choice) T C) :
    VolumeBridge (l := l) (V := V) (Label := Label) (Choice := Choice)
      T' C :=
  ⟨bridge.volume_bridge.trans
    (HodgeTheaterLink.log_volume_eq link).symm⟩

set_option linter.checkUnivs false in
theorem volumeBridge_of_history {T : HodgeTheater.{ua, uv, upi, umon} l V}
    (C : Carrier Label Choice)
    (history : HodgeTheaterHistory.{ua, uv, upi, umon} l V T)
    (bridge : VolumeBridge (l := l) (V := V) (Label := Label)
      (Choice := Choice) history.terminal C) :
    VolumeBridge (l := l) (V := V) (Label := Label) (Choice := Choice)
      T C :=
  ⟨bridge.volume_bridge.trans
    (HodgeTheaterLink.log_volume_eq history.composite).symm⟩

/-- A constant carrier: level is the identity on `Nat`, Ind1/Ind2 act
    trivially, Ind3 adds, the log-volume is the constant `v`, and the
    possible image is `{v}`.  It exhibits the carrier-side freedom used in
    the negative result below. -/
def constantVolumeCarrier (v : Real) : Carrier Label Nat where
  core :=
    { base := 0
      level := id
      ind1 := fun _ c => c
      ind2 := fun _ c => c
      ind3 := fun n c => c + n
      ind1_zero := fun _ => rfl
      ind1_add := fun _ _ _ => rfl
      ind1_inverse := fun _ _ => rfl
      ind2_zero := fun _ => rfl
      ind2_add := fun _ _ _ => rfl
      ind2_inverse := fun _ _ => rfl
      ind3_zero := fun _ => rfl
      ind3_add := fun m n c => (Nat.add_assoc c m n).symm
      ind1_ind2_commute := fun _ _ _ => rfl
      ind1_ind3_commute := fun _ _ _ => rfl
      ind2_ind3_commute := fun _ _ _ => rfl
      ind1_level := fun _ _ => rfl
      ind2_level := fun _ _ => rfl
      ind3_level := fun n c => Nat.le_add_right c n }
  profile :=
    { logVolume := fun _ => v
      possibleImage := fun _ => {v}
      ind1_invariant := fun _ _ => rfl
      ind2_invariant := fun _ _ => rfl
      ind3_upper := fun _ _ => le_rfl
      possibleImage_nonempty := fun _ => ⟨v, rfl⟩
      possibleImage_ind1 := fun _ _ => rfl
      possibleImage_ind2 := fun _ _ => rfl
      possibleImage_ind3 := fun _ _ z hz => ⟨z, hz, le_rfl⟩ }
  connector := fun _ _ => []
  connector_horizontal := fun _ _ _ hstep => absurd hstep (by simp)
  connector_target_same_level := by
    intro a b hlevel
    simpa using hlevel
  ind3_level_eq := fun n c => rfl

/- A precise negative result: on any fixed theater the log-volume bridge
    cannot hold for every carrier.  Two constant carriers with log-volumes
    `0` and `1` would force `0 = 1`.  No property of the theta packet
    beyond a fixed log-volume is used. -/
set_option linter.checkUnivs false in
theorem not_forall_volumeBridge
    (T : HodgeTheater.{ua, uv, upi, umon} l V) :
    ¬ (∀ C : Carrier Label Nat,
      VolumeBridge (l := l) (V := V) (Label := Label) (Choice := Nat)
        T C) := by
  intro hall
  have hzero := (hall (constantVolumeCarrier (0 : Real))).volume_bridge
  have hone := (hall (constantVolumeCarrier (1 : Real))).volume_bridge
  have h01 : (0 : Real) = 1 := hzero.trans hone.symm
  exact (by norm_num : (0 : Real) ≠ 1) h01

/- For every theater some carrier carries the bridge: the constant carrier
    at the theater's own log-volume.  This is the matching existence
    direction of the card, not a generic proof of the bridge. -/
set_option linter.checkUnivs false in
theorem exists_carrier_volumeBridge
    (T : HodgeTheater.{ua, uv, upi, umon} l V) :
    ∃ C : Carrier Label Nat,
      VolumeBridge (l := l) (V := V) (Label := Label) (Choice := Nat)
        T C :=
  ⟨constantVolumeCarrier T.thetaPacket.logVolume, ⟨rfl⟩⟩

/- The Q(i)-at-5 bridge, recovered from the frozen concrete instance. -/
set_option linter.checkUnivs false in
theorem concreteVolumeBridge (l : PrimeGeFive) :
    VolumeBridge (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      (T := ConcreteSourceHistoryLinkBridge.sourceTheater l)
      (C := SourceFiniteParameterized.carrier l) :=
  ⟨SourceFiniteMultiradial.emptyRouteOutput_log_volume l⟩

/-- The Q(i)-at-5 record, obtained through the single-card reduction. -/
theorem concreteRecord_via_volumeBridge (l : PrimeGeFive) :
    ∃ input : Input (l := l) (V := FinitePrimePlace 2 7)
        (Label := ConcreteFiniteTheorem311.finiteLabel l)
        (Choice := ConcreteFiniteTheorem311.ProcessionChoice l),
      input.theater = ConcreteSourceHistoryLinkBridge.sourceTheater l ∧
      input.carrier = SourceFiniteParameterized.carrier l :=
  (record_exists_iff_volumeBridge (l := l) (V := FinitePrimePlace 2 7)
    (Label := ConcreteFiniteTheorem311.finiteLabel l)
    (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
    (T := ConcreteSourceHistoryLinkBridge.sourceTheater l)
    (C := SourceFiniteParameterized.carrier l)).mpr (concreteVolumeBridge l)

/-! ## Card 1b: existence at the literal-record level, for every theater

The conditional form `record_exists_iff_volumeBridge` prescribes the carrier.
The `Input` record itself does not: the carrier is a field of the record.
With the carrier free, a record exists for *every* Hodge theater and every
prescribed dependent history: take the constant carrier at the theater's own
log-volume, so the volume bridge holds, and the route normal form is the
generic `route_normal_form_holds`.  This closes existence at the literal
record level only: the source-facing question asks for the paper's own
carrier (the arithmetic carrier compatible with the theater's procession
data), and that single compatibility remains open.  It is recorded as the
named card `IUT-III.source-procession-boundary.intended-carrier-bridge` in
this file's audit section. -/

set_option linter.checkUnivs false in
def auxiliaryCarrierRecord (T : HodgeTheater.{ua, uv, upi, umon} l V)
    (H : HodgeTheaterHistory.{ua, uv, upi, umon} l V T) :
    Input (l := l) (V := V) (Label := Label) (Choice := Nat) :=
  Input.ofBridgeData T H (constantVolumeCarrier T.thetaPacket.logVolume)
    ⟨rfl, route_normal_form_holds _⟩

set_option linter.checkUnivs false in
@[simp] theorem auxiliaryCarrierRecord_theater
    (T : HodgeTheater.{ua, uv, upi, umon} l V)
    (H : HodgeTheaterHistory.{ua, uv, upi, umon} l V T) :
    (auxiliaryCarrierRecord (Label := Label) T H).theater = T :=
  rfl

set_option linter.checkUnivs false in
@[simp] theorem auxiliaryCarrierRecord_history
    (T : HodgeTheater.{ua, uv, upi, umon} l V)
    (H : HodgeTheaterHistory.{ua, uv, upi, umon} l V T) :
    (auxiliaryCarrierRecord (Label := Label) T H).history = H :=
  rfl

set_option linter.checkUnivs false in
@[simp] theorem auxiliaryCarrierRecord_carrier
    (T : HodgeTheater.{ua, uv, upi, umon} l V)
    (H : HodgeTheaterHistory.{ua, uv, upi, umon} l V T) :
    (auxiliaryCarrierRecord (Label := Label) T H).carrier =
      constantVolumeCarrier (Label := Label) T.thetaPacket.logVolume :=
  rfl

set_option linter.checkUnivs false in
@[simp] theorem auxiliaryCarrierRecord_base_packetVolume
    (T : HodgeTheater.{ua, uv, upi, umon} l V)
    (H : HodgeTheaterHistory.{ua, uv, upi, umon} l V T) :
    (auxiliaryCarrierRecord (Label := Label) T H).packetVolume
        (auxiliaryCarrierRecord (Label := Label) T H).baseChoice =
      T.thetaPacket.logVolume :=
  rfl

set_option linter.checkUnivs false in
theorem exists_record_arbitraryTheater
    (T : HodgeTheater.{ua, uv, upi, umon} l V) :
    ∃ input : Input (l := l) (V := V) (Label := Label) (Choice := Nat),
      input.theater = T :=
  ⟨auxiliaryCarrierRecord (Label := Label) T (HodgeTheaterHistory.singleton T),
    auxiliaryCarrierRecord_theater (Label := Label) T
      (HodgeTheaterHistory.singleton T)⟩

set_option linter.checkUnivs false in
theorem exists_record_arbitraryTheater_history
    (T : HodgeTheater.{ua, uv, upi, umon} l V)
    (H : HodgeTheaterHistory.{ua, uv, upi, umon} l V T) :
    ∃ input : Input (l := l) (V := V) (Label := Label) (Choice := Nat),
      input.theater = T ∧ HEq input.history H :=
  ⟨auxiliaryCarrierRecord (Label := Label) T H,
    auxiliaryCarrierRecord_theater (Label := Label) T H, HEq.rfl⟩

end SourceProcessionBoundary

end

end LeanFormal.IUT
namespace LeanFormal.IUT.Audit

def sourceProcessionRecordExistenceGeneral : Obligation :=
  { id := "IUT-III.source-procession-record-existence-general"
    source :=
      "IUT III, Theorem 3.11, (i), (a); [IUTchI], Proposition 6.9, (ii) " ++
        "(corpus I.txt:9811)"
    status := VerificationStatus.conditional
    note :=
      "For an arbitrary parameterized carrier the route normal form is " ++
        "proved unconditionally (route_normal_form_holds), so record " ++
        "existence at a fixed theater/carrier pair is equivalent to the " ++
        "single named condition VolumeBridge " ++
        "(record_exists_iff_volumeBridge): the carrier log-volume at the " ++
        "core base equals the theater theta-packet log-volume. The bridge " ++
        "is not provable for every carrier (not_forall_volumeBridge: two " ++
        "constant carriers give 0 = 1), but it transports along " ++
        "Hodge-theater links and dependent histories " ++
        "(volumeBridge_of_link, volumeBridge_of_history), a compatible " ++
        "carrier exists for every theater (exists_carrier_volumeBridge), " ++
        "and the Q(i)-at-5 bridge is recovered (concreteVolumeBridge, " ++
        "concreteRecord_via_volumeBridge). The compatibility of the " ++
        "paper's carrier with an arbitrary source theater remains a " ++
        "source input; this entry does not claim it."
    dependsOn :=
      [ "IUT-III.source-procession-record-existence",
        "IUT-I.hodge-theater-link-log-volume-transport",
        "IUT-I.hodge-theater-history-composition",
        "IUT-III.parametric-D-stage-certificates" ] }

/-- Final card (line to standby): what remains of the source-facing boundary
    note after the auxiliary-carrier existence is proved -- the paper's own
    carrier and its single compatibility equation with the theater, with the
    blocked routes and the reopening requirements frozen below. -/
def sourceProcessionRecordIntendedCarrierCard : Obligation :=
  { id := "IUT-III.source-procession-boundary.intended-carrier-bridge"
    source :=
      "IUT III, Theorem 3.11, (i), (a) (theta-packet log-volumes); " ++
        "procession-normalized mono-analytic log-volumes of Proposition " ++
        "3.9, (ii); SourceProcessionBoundary.lean:515-528 (the boundary " ++
        "note)"
    status := VerificationStatus.pending
    note :=
      "Final card (line to standby).  Object: the paper's own carrier C_T " ++
        "for an arbitrary source Hodge theater T -- the arithmetic carrier " ++
        "compatible with T's procession data -- with its single " ++
        "compatibility equation C_T.profile.logVolume C_T.core.base = " ++
        "T.thetaPacket.logVolume.  Quantifier: for every Hodge theater T; " ++
        "the dependent history H is free (by record_exists_iff_volumeBridge " ++
        "the one equation yields the record for (T, C_T) with any " ++
        "prescribed H).  Assumptions: a source-side construction of C_T " ++
        "from the arithmetic input -- the seven-object boundary " ++
        "(CarrierConnectorSpecification.CarrierConnectorDatum; CC.1/CC.2) " ++
        "plus the Definition 3.1 (D3)/(D4) reduction line " ++
        "(IUTI/InitialTheta), which is open.  Conclusion: VolumeBridge T " ++
        "C_T, hence a nonempty SourceProcessionBoundary.Input record at " ++
        "(T, C_T).  Consumers: the Theorem 3.11 source chain reached from " ++
        "the boundary note SourceProcessionBoundary.lean:515-528.  What is " ++
        "already available in this file: the route normal form is " ++
        "unconditional (route_normal_form_holds) and auxiliary-carrier " ++
        "existence is proved (auxiliaryCarrierRecord, " ++
        "exists_record_arbitraryTheater, exists_record_arbitraryTheater_history) " ++
        "-- so only the single equation above is missing.  Three routes " ++
        "attempted and blocked: (a) derive a carrier from the theater " ++
        "itself -- the theater fields are InitialThetaArithmeticData, " ++
        "FPrimeStrip, FiniteThetaPacket (HodgeTheaterCore.lean:31-34), and " ++
        "no construction from them to a Label/Choice Carrier exists in the " ++
        "tree (the arithmetic-input reduction is open at the " ++
        "IUTI/InitialTheta Definition 3.1 (D3)/(D4) line); (b) force the " ++
        "intended carrier from the seven-object boundary " ++
        "(CarrierConnectorDatum) -- it supplies CC.1/CC.2 but no " ++
        "log-volume equation with the theta packet; (c) transfer a seed " ++
        "bridge along links/histories (volumeBridge_of_link, " ++
        "volumeBridge_of_history) -- every transfer needs an existing " ++
        "bridge for a related pair, and the only concrete seed is the " ++
        "Q(i)-at-5 instance (concreteVolumeBridge), so no seed exists for " ++
        "an arbitrary source.  Reopening requires one of: a carrier " ++
        "construction from the arithmetic input (the (D3)/(D4) line), a " ++
        "log-volume equation supplied through the connector datum, or one " ++
        "seed bridge for an arbitrary source.  Relation to the " ++
        "transport-supply card `IUT-III.source-APT-transport-supply` " ++
        "(APT.lean:457; cross-line entry #11): that card is the (xi-b) " ++
        "processional transport supply consuming (IPL)+(SHE) evidence; " ++
        "this card is the record/carrier existence face of the same " ++
        "missing source layer.  Neither card entails the other, and the " ++
        "auxiliary-carrier existence in this file is not an impersonation " ++
        "of either.  PARKED at this named card."
    dependsOn :=
      [ "IUT-III.source-procession-boundary",
        "IUT-III.source-procession-record-existence-general" ] }

end LeanFormal.IUT.Audit
