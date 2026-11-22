import LeanFormal.IUT.IUTIII.Theorem311.SourceFaithfulBoundary
import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteParameterized
import LeanFormal.IUT.IUTIII.Theorem311.Output.MultiradialAlgorithmGeneralRouteNormalForm
import Mathlib.Tactic

/-!
# Carrier connector specification: the field-level boundary of the source carrier

Remaining card (1) of `IUT-III.multiradial-algorithm` asks for the carrier
instance from the actual IUT I--II data: the `connector` field and the
`ind3_level_eq` field of `ParametricTheorem311.Carrier`
(ParametricCarrier.lean:28-33).  This file freezes the field-level map from the
seven source objects of `Theorem311Source.DerivedPrerequisiteInput`
(SourceFaithfulBoundary.lean:278-312) to the carrier, together with the exact
named datum for the missing fields.

## Paper location

IUT III, Theorem 3.11, (i) (Multiradial Representation; corpus III.txt:9164):
after fixing initial Theta-data ([IUTchI], Definition 3.1; corpus III.txt:9152-9155),
the procession of D-prime-strips `Prc(n,o D_T)` is obtained via the natural
functor of [IUTchI], Proposition 6.9, (ii) (corpus III.txt:9174;
corpus I.txt:9811-9826); the data (a) procession-normalized log-volumes
(corpus III.txt:9176-9191), (b) splitting monoid (corpus III.txt:9192-9205),
(c) global Frobenioids with global degrees (corpus III.txt:9222-9253) are
regarded up to (Ind1) automorphisms of the procession of D-prime-strips
(corpus III.txt:9258-9260) and (Ind2) (corpus III.txt:9261-9272); the
representation `n,o RLGP` is constructed via an algorithm in the procession
functorial with respect to isomorphisms of processions
(corpus III.txt:9273-9276).  The (Ind3) indeterminacy is the upper
semi-compatibility indeterminacy of the log-link (corpus III.txt:669,
:248, :370); it is an order law, not an equality.

## Field-level map

Status: `proved` = the conversion or instance exists in the tree; `interface` =
field of the boundary record, supplied by the caller, not an existence theorem;
`missing` = named datum introduced in this file.  Short names: SFB =
SourceFaithfulBoundary.lean, SFP = SourceFiniteParameterized.lean, SFM =
SourceFiniteMultiradial.lean.

- initial Theta-data: (output side) SFB:286 interface; outputs :1631-:1674.
- D-prime-strip procession: `Carrier.core`; SFB:318 via :81 proved.
- packet / log-volume: `Carrier.profile`; SFB:321 via :143 proved; volume
  agreement SFB:284 interface.
- vertical Kummer: (output side) SFB:287-297 interface.
- labelled Kummer: (output side) SFB:301-306 interface.
- evaluation: (output side) SFB:300, :310-312 interface.
- horizontal link: (output side) SFB:303 interface.
- procession automorphisms: `Carrier.connector`; finite Q(i)-at-5 model only,
  SFP:28-37 via SFM:234 proved; missing card CC.1 `SameLevelRouteConnector`.
- log-link level bookkeeping: `Carrier.ind3_level_eq`; upper-semi supply law
  SFB:78; finite model SFP:68 proved; missing card CC.2
  `CarrierConnectorDatum.ind3_level_eq`.

## Boundary of the claims

`SameLevelRouteConnector` and `CarrierConnectorDatum` below are specification
types: they say what it would mean to supply the missing fields.  A
specification type is not an existence claim; in particular no instance of
`CarrierConnectorDatum` is constructed for an arbitrary source input in this
file.  The non-forcing witnesses of Section 4 show that neither field follows
from the frozen supply laws.  The only instance exhibited is the finite
Q(i)-at-5 one (`finiteCarrierConnectorDatum`), and every carrier is a datum
source under the reverse direction (`CarrierConnectorDatum.ofCarrier`).
-/

namespace LeanFormal.IUT

noncomputable section

universe u v

namespace CarrierConnectorSpecification

open MultiradialKernel
open MultiradialKernel.Core
open Theorem311Source

variable {Label : Type u} {Choice : Type v} [AddGroup Label]

/-! ## 1. Specification types (specification is not an existence claim) -/

/-- The same-level route connector of a core: a horizontal route between any
    two choices of equal level.  This is CC.1 of the field-level map: the
    formal target of the procession-automorphism connection of Theorem 3.11,
    (i) (corpus III.txt:9258, :9273-9276).  It is a specification type, not an
    existence claim. -/
structure SameLevelRouteConnector (core : Core Label Choice) where
  connector : Choice → Choice → List (RouteStep Label)
  connector_horizontal : ∀ a b, ∀ step ∈ connector a b, horizontal step
  connector_target_same_level : ∀ {a b},
    core.level a = core.level b → applyRoute core (connector a b) a = b

/-- The exact named datum behind remaining card (1) of
    `IUT-III.multiradial-algorithm`: the two fields which
    `ParametricTheorem311.Carrier` demands beyond the seven-object source
    boundary `Theorem311Source.DerivedPrerequisiteInput`.  CC.1 is the
    same-level connector; CC.2 is exact additivity of the level under the
    log-link steps, which the source boundary supplies only as the upper-semi
    law `DPrimeStripProcession.ind3_level` (SourceFaithfulBoundary.lean:78).
    This is a specification type, not an existence claim. -/
structure CarrierConnectorDatum (core : Core Label Choice) where
  sameLevelConnector : SameLevelRouteConnector core
  ind3_level_eq : ∀ n c, core.level (core.ind3 n c) = core.level c + n

/-! ## 2. Conditional assembly of the carrier -/

/-- Assemble a parameterized carrier from a core, a profile, and a connector
    datum.  This is the conditional form of card (1): given the datum, the
    carrier exists; the datum itself is not constructed here. -/
def carrierOfConnectorDatum (core : Core Label Choice) (profile : Profile core)
    (datum : CarrierConnectorDatum core) :
    ParametricTheorem311.Carrier Label Choice where
  core := core
  profile := profile
  connector := datum.sameLevelConnector.connector
  connector_horizontal := datum.sameLevelConnector.connector_horizontal
  connector_target_same_level := datum.sameLevelConnector.connector_target_same_level
  ind3_level_eq := datum.ind3_level_eq

/-- The source-level conditional carrier: the procession and packet of the
    seven-object boundary supply the core and profile (rows 2-3 of the table);
    only the connector datum is demanded. -/
def sourceCarrierOfConnectorDatum
    (I : DerivedPrerequisiteInput Label Choice)
    (datum : CarrierConnectorDatum I.core) :
    ParametricTheorem311.Carrier Label Choice :=
  carrierOfConnectorDatum I.core I.profile datum

@[simp] theorem sourceCarrierOfConnectorDatum_core
    (I : DerivedPrerequisiteInput Label Choice)
    (datum : CarrierConnectorDatum I.core) :
    (sourceCarrierOfConnectorDatum I datum).core = I.core := rfl

@[simp] theorem sourceCarrierOfConnectorDatum_profile
    (I : DerivedPrerequisiteInput Label Choice)
    (datum : CarrierConnectorDatum I.core) :
    (sourceCarrierOfConnectorDatum I datum).profile = I.profile := rfl

@[simp] theorem carrierOfConnectorDatum_connector
    (core : Core Label Choice) (profile : Profile core)
    (datum : CarrierConnectorDatum core) :
    (carrierOfConnectorDatum core profile datum).connector =
      datum.sameLevelConnector.connector := rfl

/-- Reverse direction: every carrier is a connector datum for its own core. -/
def CarrierConnectorDatum.ofCarrier
    (carrier : ParametricTheorem311.Carrier Label Choice) :
    CarrierConnectorDatum carrier.core where
  sameLevelConnector :=
    { connector := carrier.connector
      connector_horizontal := carrier.connector_horizontal
      connector_target_same_level := carrier.connector_target_same_level }
  ind3_level_eq := carrier.ind3_level_eq

/-- The assembly is a left inverse of the reverse direction. -/
theorem carrierOfConnectorDatum_ofCarrier
    (carrier : ParametricTheorem311.Carrier Label Choice) :
    carrierOfConnectorDatum carrier.core carrier.profile
      (CarrierConnectorDatum.ofCarrier carrier) = carrier := by
  cases carrier
  rfl

/-- The finite Q(i)-at-5 carrier is an instance of the specification.  This
    exhibits inhabitation of the specification type for the finite model only;
    it is not a source-level instance. -/
def finiteCarrierConnectorDatum (l : PrimeGeFive) :
    CarrierConnectorDatum (SourceFiniteParameterized.carrier l).core :=
  CarrierConnectorDatum.ofCarrier (SourceFiniteParameterized.carrier l)

/-! ## 3. Consumer receipts: the Section-14/15 stack applies once the datum is
supplied -/

/-- The general route normal form (residual card (2) of
    `IUT-III.multiradial-algorithm`, closed in `MultiradialAlgorithmGeneral`)
    applies to the source carrier assembled from the connector datum. -/
theorem sourceCarrierOfConnectorDatum_routeNormalForm
    (I : DerivedPrerequisiteInput Label Choice)
    (datum : CarrierConnectorDatum I.core) :
    MultiradialAlgorithmReduction.RouteNormalForm
      (sourceCarrierOfConnectorDatum I datum) :=
  MultiradialAlgorithmGeneral.routeNormalForm_general _

/-- The carrier-level algorithm contract applies to the source carrier
    assembled from the connector datum. -/
theorem sourceCarrierOfConnectorDatum_algorithmContract
    (I : DerivedPrerequisiteInput Label Choice)
    (datum : CarrierConnectorDatum I.core) :
    MultiradialAlgorithmReduction.CarrierAlgorithmContract
      (sourceCarrierOfConnectorDatum I datum) :=
  MultiradialAlgorithmReduction.carrierAlgorithmContract _

/-! ## 4. Non-forcing witnesses

  The datum is not a consequence of the frozen supply laws: the two statements
  below exhibit models satisfying every supplied law where the demanded field
  fails. -/

/-- Degenerate procession: one choice, constant level, constant actions. -/
private def trivialProcessionOnUnits : DPrimeStripProcession ℤ Unit where
  base := ()
  level := fun _ => 0
  ind1 := fun _ _ => ()
  ind2 := fun _ _ => ()
  ind3 := fun _ _ => ()
  ind1_zero := fun _ => rfl
  ind1_add := fun _ _ _ => rfl
  ind1_inverse := fun _ _ => rfl
  ind2_zero := fun _ => rfl
  ind2_add := fun _ _ _ => rfl
  ind2_inverse := fun _ _ => rfl
  ind3_zero := fun _ => rfl
  ind3_add := fun _ _ _ => rfl
  ind1_ind2_commute := fun _ _ _ => rfl
  ind1_ind3_commute := fun _ _ _ => rfl
  ind2_ind3_commute := fun _ _ _ => rfl
  ind1_level := fun _ _ => rfl
  ind2_level := fun _ _ => rfl
  ind3_level := fun _ _ => Nat.le_refl 0

/-- Exact additivity of the level under log-link steps does not follow from the
    frozen procession laws: the source boundary supplies only
    `level c ≤ level (ind3 n c)` (SourceFaithfulBoundary.lean:78), and the
    countermodel above satisfies every procession law while failing
    additivity at `n = 1`. -/
theorem procession_laws_do_not_force_ind3_additivity :
    ¬ (∀ (P : DPrimeStripProcession ℤ Unit), ∀ n c,
      P.level (P.ind3 n c) = P.level c + n) := by
  intro h
  have h₁ : (0 : Nat) = 0 + 1 := h trivialProcessionOnUnits 1 ()
  omega

/-- Degenerate core: two choices of equal level, all actions the identity. -/
private def flatCoreOnBool : Core ℤ Bool where
  base := false
  level := fun _ => 0
  ind1 := fun _ c => c
  ind2 := fun _ c => c
  ind3 := fun _ c => c
  ind1_zero := fun _ => rfl
  ind1_add := fun _ _ _ => rfl
  ind1_inverse := fun _ _ => rfl
  ind2_zero := fun _ => rfl
  ind2_add := fun _ _ _ => rfl
  ind2_inverse := fun _ _ => rfl
  ind3_zero := fun _ => rfl
  ind3_add := fun _ _ _ => rfl
  ind1_ind2_commute := fun _ _ _ => rfl
  ind1_ind3_commute := fun _ _ _ => rfl
  ind2_ind3_commute := fun _ _ _ => rfl
  ind1_level := fun _ _ => rfl
  ind2_level := fun _ _ => rfl
  ind3_level := fun _ _ => Nat.le_refl 0

/-- A same-level connector does not follow from the core laws: the countermodel
    above satisfies every `Core` law, but no connector at all can send `false`
    to `true`, because every step of every route acts as the identity. -/
theorem core_laws_do_not_force_same_level_connector :
    ¬ ∃ connector : Bool → Bool → List (RouteStep ℤ),
      (∀ a b, ∀ step ∈ connector a b, horizontal step) ∧
      (∀ {a b : Bool}, flatCoreOnBool.level a = flatCoreOnBool.level b →
        applyRoute flatCoreOnBool (connector a b) a = b) := by
  rintro ⟨connector, _hhorizontal, htarget⟩
  have hfalse := htarget (a := false) (b := true) rfl
  have hconst : ∀ (route : List (RouteStep ℤ)) (c : Bool),
      applyRoute flatCoreOnBool route c = c := by
    intro route
    induction route with
    | nil => intro c; rfl
    | cons step rest ih =>
        intro c
        rw [applyRoute_cons]
        rw [ih]
        cases step with
        | ind1 g => rfl
        | ind2 g => rfl
        | ind3 n => rfl
  rw [hconst (connector false true) false] at hfalse
  exact Bool.false_ne_true hfalse

end CarrierConnectorSpecification

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the carrier connector specification. -/
def carrierConnectorSpecificationRecord : Obligation :=
  { id := "IUT-III.multiradial-algorithm.carrier-connector-specification"
    source :=
      "IUT III, Theorem 3.11, (i) (corpus III.txt:9151, :9164-9175, " ++
        ":9258-9260, :9273-9276); [IUTchI], Proposition 6.9, (i)/(ii) " ++
        "(corpus I.txt:9811-9826); (Ind3) upper-semi compatibility " ++
        "(corpus III.txt:669)"
    status := VerificationStatus.conditional
    note :=
      "Field-level specification of remaining card (1) of " ++
        "`IUT-III.multiradial-algorithm` (connector and level-additivity). " ++
        "`SameLevelRouteConnector` and `CarrierConnectorDatum` are " ++
        "specification types, not existence claims. " ++
        "`carrierOfConnectorDatum` and `sourceCarrierOfConnectorDatum` " ++
        "assemble the carrier conditionally on the datum; " ++
        "`sourceCarrierOfConnectorDatum_routeNormalForm` and " ++
        "`sourceCarrierOfConnectorDatum_algorithmContract` receive the " ++
        "unconditional general route normal form and the carrier-level " ++
        "algorithm contract once the datum is supplied; " ++
        "`CarrierConnectorDatum.ofCarrier` and " ++
        "`carrierOfConnectorDatum_ofCarrier` give the reverse direction and " ++
        "the round trip; `finiteCarrierConnectorDatum` exhibits the finite " ++
        "Q(i)-at-5 instance.  Non-forcing witnesses: " ++
        "`procession_laws_do_not_force_ind3_additivity` and " ++
        "`core_laws_do_not_force_same_level_connector`.  The datum itself is " ++
        "not constructed for an arbitrary source; no existence claim is made."
    dependsOn :=
      [ "IUT-III.multiradial-algorithm",
        "IUT-III.theorem-3.11-explicit-prerequisite-boundary",
        "IUT-III.multiradial-algorithm.general-route-normal-form",
        "IUT-I-II.prime-strips-frobenioids" ] }

end LeanFormal.IUT.Audit
