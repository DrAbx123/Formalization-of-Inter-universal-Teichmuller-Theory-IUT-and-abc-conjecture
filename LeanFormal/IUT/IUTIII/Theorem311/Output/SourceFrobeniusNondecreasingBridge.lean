import LeanFormal.IUT.IUTIII.Theorem311.Output.CarrierConnectorSpecification
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Source Frobenius nondecreasing witness from the CC.2 level datum

This file answers the CC.2 request block routed from the Leibniz Step-(x) line
(report line 349, the CC.2 request-block evaluation; relay REQ-2): from the
CC.2 source datum
`CarrierConnectorSpecification.CarrierConnectorDatum.ind3_level_eq`
-- exact additivity of the level under the (Ind3) log-link steps -- produce the
source-level Frobenius nondecreasing witness, in the monotone interface form
consumed by the conditional Frobenius-compatibility records
(`FrobeniusUpperSemiCompatibility`-shaped: an endomorphism together with a
`level`-monotonicity field).  The bridge is conditional on the datum; the datum
itself remains the open source-level card (source carrier existence, Boyle
line; report sections 16-17).  No source-level existence claim is made here.

## Frozen statements

- `ind3_level_monotone_of_carrierConnectorDatum`: for a core carrying a CC.2
  datum, `level c ≤ level (ind3 n c)` for every `n` and `c`.
- `ind3_level_strict_of_carrierConnectorDatum`: for `0 < n`,
  `level c < level (ind3 n c)`; this strict form does not follow from the
  frozen upper-semi supply law `Core.ind3_level` (which allows constant
  level), only from exact additivity.
- `frobeniusStep_level_strict_of_carrierConnectorDatum`: the canonical
  Frobenius step `n = 1` (the stage-one (Ind3) lift of the Step-(x) docking).
- `FrobeniusNondecreasingWitness`: named witness record (`frobenius` plus its
  monotonicity law), with the datum and carrier constructors.
- Route receipts: `carrier_ind3_level_strict` (entry through a full carrier,
  via `CarrierConnectorDatum.ofCarrier`),
  `sourceCarrierOfConnectorDatum_ind3_level_monotone` (the conditional source
  carrier assembled in `CarrierConnectorSpecification`), and the finite
  Q(i)-at-5 instance `finiteCarrier_ind3_level_strict`.
- One-directional docking: `constantLevelTrivialCore_*` shows that the
  nondecreasing witness alone does not force the CC.2 equality, so the exact
  datum is strictly stronger than the monotone interface form.

## Paper location

IUT III, Theorem 3.11, (i); the (Ind3) upper-semi compatibility of the
log-link is an order law, not an equality (corpus III.txt:669, :248, :370);
the stage-one (Ind3) lift as the canonical compatible Frobenius action is the
Step-(x) reading of Remark 3.12.3, (v) (corpus III.txt:11589-11619).

## Boundary

`ind3_level_monotone_of_carrierConnectorDatum` is a conversion lemma: the weak
nondecreasing form is also available from the frozen law `Core.ind3_level`, so
the content of the bridge is (i) the docking of the exact datum form to the
monotone interface form and (ii) the strict upgrade, which needs the datum.
The Kummer-image face (`kummer_mono` of the conditional layer records) is not
a level statement and is not supplied here. -/

namespace LeanFormal.IUT

noncomputable section

universe u v

namespace SourceFrobeniusNondecreasingBridge

open MultiradialKernel
open Theorem311Source
open CarrierConnectorSpecification

variable {Label : Type u} {Choice : Type v} [AddGroup Label]

/-! ## 1. The bridge: exact additivity implies the nondecreasing witness -/

/-- CC.2 bridge, nondecreasing form: the exact level additivity of a carrier
    connector datum implies that every (Ind3) log-link step does not lower
    the level.  This is the field-level docking from the exact-additivity
    form of `CarrierConnectorDatum.ind3_level_eq` to the monotone interface
    form. -/
theorem ind3_level_monotone_of_carrierConnectorDatum {core : Core Label Choice}
    (datum : CarrierConnectorDatum core) (n : Nat) (c : Choice) :
    core.level c ≤ core.level (core.ind3 n c) :=
  calc core.level c ≤ core.level c + n := Nat.le_add_right _ _
    _ = core.level (core.ind3 n c) := (datum.ind3_level_eq n c).symm

/-- Strict upgrade of the bridge: a positive step raises the level strictly.
    This does not follow from the frozen upper-semi law `Core.ind3_level`
    (which is satisfied by a constant level), only from exact additivity. -/
theorem ind3_level_strict_of_carrierConnectorDatum {core : Core Label Choice}
    (datum : CarrierConnectorDatum core) {n : Nat} (hn : 0 < n) (c : Choice) :
    core.level c < core.level (core.ind3 n c) :=
  (lt_add_of_pos_right (core.level c) hn).trans_eq
    (datum.ind3_level_eq n c).symm

/-- Canonical Frobenius step `n = 1`: the stage-one (Ind3) lift raises the
    level strictly under the CC.2 datum. -/
theorem frobeniusStep_level_strict_of_carrierConnectorDatum {core : Core Label Choice}
    (datum : CarrierConnectorDatum core) (c : Choice) :
    core.level c < core.level (core.ind3 1 c) :=
  ind3_level_strict_of_carrierConnectorDatum datum Nat.one_pos c

/-! ## 2. Named witness record -/

/-- Source-level Frobenius nondecreasing witness: an endomorphism of the
    choices together with the law that it never lowers the level.  This is
    the `Core`-level counterpart of the monotone interface shape consumed by
    the conditional Frobenius-compatibility records (Leibniz Step-(x) line:
    `FrobeniusUpperSemiCompatibility.level_monotone`,
    `LayerFrobeniusCompatibility.kummer_mono`).  A witness record is not an
    existence claim about the source. -/
structure FrobeniusNondecreasingWitness (core : Core Label Choice) where
  frobenius : Choice → Choice
  frobenius_nondecreasing : ∀ c, core.level c ≤ core.level (frobenius c)

namespace FrobeniusNondecreasingWitness

/-- The witness law, as a named accessor. -/
theorem level_le {core : Core Label Choice}
    (W : FrobeniusNondecreasingWitness core) (c : Choice) :
    core.level c ≤ core.level (W.frobenius c) :=
  W.frobenius_nondecreasing c

end FrobeniusNondecreasingWitness

/-- The CC.2 datum supplies the witness with the canonical Frobenius action:
    the stage-one (Ind3) lift `ind3 1`. -/
def FrobeniusNondecreasingWitness.ofCarrierConnectorDatum {core : Core Label Choice}
    (datum : CarrierConnectorDatum core) : FrobeniusNondecreasingWitness core where
  frobenius := core.ind3 1
  frobenius_nondecreasing := fun c =>
    ind3_level_monotone_of_carrierConnectorDatum datum 1 c

/-- Carrier entry: every full parametric carrier yields the witness for its
    own core, through `CarrierConnectorDatum.ofCarrier`. -/
def FrobeniusNondecreasingWitness.ofCarrier
    (carrier : ParametricTheorem311.Carrier Label Choice) :
    FrobeniusNondecreasingWitness carrier.core :=
  FrobeniusNondecreasingWitness.ofCarrierConnectorDatum
    (CarrierConnectorDatum.ofCarrier carrier)

/-! ## 3. Route receipts: carrier, source assembly, finite instance -/

/-- Route through a full carrier (`CarrierConnectorDatum.ofCarrier`): the
    level bookkeeping of a parametric carrier raises strictly along positive
    log-link steps. -/
theorem carrier_ind3_level_strict
    (carrier : ParametricTheorem311.Carrier Label Choice) {n : Nat} (hn : 0 < n)
    (c : Choice) :
    carrier.core.level c < carrier.core.level (carrier.core.ind3 n c) :=
  ind3_level_strict_of_carrierConnectorDatum
    (CarrierConnectorDatum.ofCarrier carrier) hn c

/-- Consumer receipt: on the conditional source carrier assembled in
    `CarrierConnectorSpecification` from the seven-object boundary `I` and a
    CC.2 datum, the (Ind3) steps do not lower the level. -/
theorem sourceCarrierOfConnectorDatum_ind3_level_monotone
    (I : DerivedPrerequisiteInput Label Choice)
    (datum : CarrierConnectorDatum I.core) (n : Nat) (c : Choice) :
    (sourceCarrierOfConnectorDatum I datum).core.level c ≤
      (sourceCarrierOfConnectorDatum I datum).core.level
        ((sourceCarrierOfConnectorDatum I datum).core.ind3 n c) :=
  ind3_level_monotone_of_carrierConnectorDatum datum n c

/-- Finite Q(i)-at-5 instance: the strict nondecreasing witness on the finite
    parameterized carrier core, supplied by `finiteCarrierConnectorDatum`. -/
theorem finiteCarrier_ind3_level_strict (l : PrimeGeFive) {n : Nat} (hn : 0 < n)
    (c : SourceFiniteParameterized.Choice l) :
    (SourceFiniteParameterized.carrier l).core.level c <
      (SourceFiniteParameterized.carrier l).core.level
        ((SourceFiniteParameterized.carrier l).core.ind3 n c) :=
  ind3_level_strict_of_carrierConnectorDatum
    (finiteCarrierConnectorDatum l) hn c

/-! ## 4. One-directional docking: the witness does not force the datum -/

/-- Degenerate core: constant level, all actions the identity.  It satisfies
    every `Core` law, in particular the frozen upper-semi law `ind3_level`. -/
private def constantLevelTrivialCore : Core Int Bool where
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

/-- The weak nondecreasing witness holds on the degenerate core: the weak form
    needs no datum (it is the frozen law `Core.ind3_level`). -/
theorem constantLevelTrivialCore_ind3_level_monotone (c : Bool) :
    constantLevelTrivialCore.level c ≤
      constantLevelTrivialCore.level (constantLevelTrivialCore.ind3 1 c) :=
  Nat.le_refl 0

/-- The strict Frobenius-step witness fails on the degenerate core: strictness
    is not available from the frozen laws. -/
theorem constantLevelTrivialCore_not_frobeniusStep_strict :
    ¬ (∀ c : Bool, constantLevelTrivialCore.level c <
      constantLevelTrivialCore.level (constantLevelTrivialCore.ind3 1 c)) :=
  fun h => absurd (h false) (Nat.lt_irrefl 0)

/-- The CC.2 datum fails on the degenerate core (at `n = 1` it reads
    `0 = 0 + 1`).  Together with the weak witness above this shows that the
    docking "datum implies witness" is strictly one-directional: the monotone
    witness does not supply the exact datum, so the source-level CC.2 card
    remains a real demand even when a monotone interface is available. -/
theorem constantLevelTrivialCore_not_ind3_level_eq :
    ¬ (∀ n (c : Bool), constantLevelTrivialCore.level
        (constantLevelTrivialCore.ind3 n c) =
      constantLevelTrivialCore.level c + n) := by
  intro h
  have h_one : (0 : Nat) = 0 + 1 := h 1 false
  omega

end SourceFrobeniusNondecreasingBridge

end

end LeanFormal.IUT
