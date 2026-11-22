import LeanFormal.IUT.IUTIII.Theorem311.SourceOutputResidualAttack
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31CarrierConsolidation
import LeanFormal.IUT.Audit.Status
import Mathlib.Tactic

/-!
# Stage C of the procession residual: trace bridge and family-law supply

Task (2026-10-16, `estimates-rec8` stage C): attack the residual `P`
(procession) of the item-17 source-input card along two new routes.

* r4 (bridge transport): Bernoulli's carrier consolidation proves
  `SourceDefinition31Data l ≃ StageConstructionTrace l`
  (`sourceStageConstructionTraceEquiv`).  Verdict frozen here: the bridge
  transports a construction exactly and losslessly, but it cannot lower
  the supply: the two carriers carry the same fields, so a trace-side
  construction needs exactly the clause witnesses a contract-side
  construction needs.  Existence transports:
  `nonempty_stageConstructionTrace_iff_definition31Data`; exactness:
  `stageConstructionTrace_transport_roundtrip`.

* r5 (family laws as source): the family-law layer
  (`SourceHodgeTheaterFamily`, law groups proved) supplies the algebra of
  a supplied family, but its own header records the open obligation
  `IUT-I.hodge-theater-family-source-reduction`: construction of a family
  from Definition 3.1 data.  A `SourceHodgeTheaterSystem` additionally
  needs the source datum `SourceDefinition31Data` and the q/scale data,
  which the family does not carry (its links are `HodgeTheaterLink`
  bundles, not the system's endo-maps).  So the family laws cannot
  replace the source datum `S`.

Positive output (reduced form): the residual `P` reduces to the single
object `S : SourceDefinition31Data`.  From `S` and a base point the
canonical identity theater system and the canonical identity LGP
procession are constructed, and item 19's composition then builds the
frozen `Theorem311Source.Input`.

Honest labels (reduced forms):

* `canonicalSourceHodgeTheaterSystem` and
  `sourceLGPProcessionOfDefinition31Data` are degenerate: identity
  theater, constant q/scale `1/2`, identity link, reflexive permutation,
  identity injections, level zero.  They carry no arithmetic content and
  are not the paper's Hodge theater or LGP procession; they exhibit only
  the shape of the consumer fields.
* The chain is conditional: `S` is supplied, never manufactured.  The
  D3-D11 source gates remain open; no degenerate selection is used to
  close them (cf. `SourceDefinition31PlacePartition.lean`:23-29).
* The general Theorem 3.11 statement is not claimed here.

Corpus anchors: IUT I, Definition 3.1 (extraction line 3122); IUT III,
Theorem 3.11 opening (III:9151-9163).
-/

namespace LeanFormal.IUT

noncomputable section

universe u v w

namespace SourceProcessionAttack

open Theorem311Source
open Theorem311Source.SourceHodgeTheaterBridge
open Theorem311Source.SourceDefinition31Root.Definition31StageKernel

/-! ## 1. r4: transport across the trace bridge -/

/-- r4 frozen statement: existence transports across the carrier
consolidation bridge in both directions.  The proof is the bridge itself,
so no clause witness is gained on either side. -/
theorem nonempty_stageConstructionTrace_iff_definition31Data
    {l : PrimeGeFive} :
    Nonempty (StageConstructionTrace.{u} l) ↔
      Nonempty (SourceDefinition31Data.{u} l) :=
  ⟨fun ⟨T⟩ => ⟨(sourceStageConstructionTraceEquiv (l := l)).symm T⟩,
   fun ⟨S⟩ => ⟨(sourceStageConstructionTraceEquiv (l := l)) S⟩⟩

/-- r4 exactness: transporting a trace to the contract side and back
returns the same trace (the bridge is lossless), so any future
trace-side construction is available on the contract side verbatim. -/
theorem stageConstructionTrace_transport_roundtrip {l : PrimeGeFive}
    (T : StageConstructionTrace.{u} l) :
    (sourceStageConstructionTraceEquiv (l := l))
        ((sourceStageConstructionTraceEquiv (l := l)).symm T) = T :=
  (sourceStageConstructionTraceEquiv (l := l)).apply_symm_apply T

/-! ## 2. The canonical identity theater system over a source datum -/

/-- The canonical identity Hodge-theater system on the choice carrier,
assembled from a Definition 3.1 source datum alone: theater `id`,
constant `qParameter`/`scale` `1/2`, identity link, reflexive
permutation; all laws hold definitionally.  Degenerate: carries no
arithmetic content and is not the paper's Hodge theater. -/
def canonicalSourceHodgeTheaterSystem {l : PrimeGeFive} {Choice : Type v}
    (S : SourceDefinition31Data.{u} l) :
    SourceHodgeTheaterSystem.{u, v, v} l where
  source := S
  source_universe_anchor := S.selectedPlaces
  index := Choice
  theaterCarrier := Choice
  theater := id
  distinct := fun _ _ h => h
  qParameter := fun _ => (1 : Real) / 2
  scale := fun _ _ => (1 : Real) / 2
  link := fun _ _ t => t
  link_refl := fun _ _ => rfl
  link_trans := fun _ _ _ _ => rfl
  q_naturality := fun _ _ => rfl
  scale_naturality := fun _ _ _ => rfl
  permutation := Equiv.refl Choice
  permutation_q := fun _ => rfl
  permutation_scale := fun _ _ => rfl

/-! ## 3. The canonical identity LGP procession over a source datum -/

/-- The canonical identity LGP procession over the same source datum on
the choice carrier: `hodge` is the canonical identity system, all three
injections are the identity, the level is zero, and the source index is
the identity. -/
def sourceLGPProcessionOfDefinition31Data {l : PrimeGeFive}
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (S : SourceDefinition31Data.{u} l) (base : Choice) :
    SourceLGPProcession.{u, v} l Label Choice where
  hodge := canonicalSourceHodgeTheaterSystem (Choice := Choice) S
  base := base
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
  ind3_level := fun _ _ => le_rfl
  source_index := id
  ind1_index := fun _ _ => rfl
  ind2_index := fun _ _ => rfl
  ind3_index := fun _ _ => rfl

/-- The `hodge` field of the canonical procession is the canonical
identity system. -/
theorem sourceLGPProcessionOfDefinition31Data_hodge {l : PrimeGeFive}
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (S : SourceDefinition31Data.{u} l) (base : Choice) :
    (sourceLGPProcessionOfDefinition31Data (Label := Label) (Choice := Choice)
        S base).hodge =
      canonicalSourceHodgeTheaterSystem (Choice := Choice) S := rfl

/-- Degeneracy summary of the canonical procession: the level is zero
and all three injections are the identity. -/
theorem sourceLGPProcessionOfDefinition31Data_degenerate {l : PrimeGeFive}
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (S : SourceDefinition31Data.{u} l) (base : Choice) :
    (∀ c : Choice,
        (sourceLGPProcessionOfDefinition31Data
            (Label := Label) (Choice := Choice) S base).level c = 0) ∧
      (∀ (g : Label) (c : Choice),
        (sourceLGPProcessionOfDefinition31Data
            (Label := Label) (Choice := Choice) S base).ind1 g c = c) ∧
      (∀ (g : Label) (c : Choice),
        (sourceLGPProcessionOfDefinition31Data
            (Label := Label) (Choice := Choice) S base).ind2 g c = c) ∧
      (∀ (n : Nat) (c : Choice),
        (sourceLGPProcessionOfDefinition31Data
            (Label := Label) (Choice := Choice) S base).ind3 n c = c) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-! ## 4. The item-17 source input from the source datum alone -/

/-- The frozen Theorem 3.11 realization built from the source datum `S`
alone and a base point, through the canonical identity theater/procession
and item 19's canonical test packet.  Conditional: `S` is the residual
source input; no source gate is closed. -/
def sourceTheorem311RealizationOfDefinition31Data {l : PrimeGeFive}
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (S : SourceDefinition31Data.{u} l) (base : Choice) :
    SourceTheorem311Realization.{u, v, w} l Label Choice :=
  SourceOutputAttack.sourceTheorem311RealizationOfProcession
    (sourceLGPProcessionOfDefinition31Data S base)

/-- The frozen `Theorem311Source.Input` from the source datum `S` alone.
Conditional construction: `S` remains the parked source residual. -/
def sourceInputOfDefinition31Data {l : PrimeGeFive}
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (S : SourceDefinition31Data.{u} l) (base : Choice) :
    Theorem311Source.Input.{u, v, w} Label Choice :=
  (sourceTheorem311RealizationOfDefinition31Data S base).input

/-- Nonemptiness form: for every supplied source datum the frozen input
package is inhabited. -/
theorem sourceInput_nonempty_of_definition31Data {l : PrimeGeFive}
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (S : SourceDefinition31Data.{u} l) (base : Choice) :
    Nonempty (Theorem311Source.Input.{u, v, w} Label Choice) :=
  ⟨sourceInputOfDefinition31Data S base⟩

end SourceProcessionAttack

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- r4 card: the trace-construction bridge transports exactly and adds
no supply. -/
def sourceProcessionTraceBridgeCard : Obligation :=
  { id :=
      "IUT-III.theorem-3.11-output.source-input-residual.procession-trace-bridge"
    source :=
      "IUT I, Definition 3.1 (line 3122); carrier consolidation leaf"
    status := VerificationStatus.provedKernel
    note :=
      "r4 of the procession-residual attack (stage C). Bridge: " ++
        "sourceStageConstructionTraceEquiv : SourceDefinition31Data l ≃ " ++
        "StageConstructionTrace l (SourceDefinition31CarrierConsolidation" ++
        ":216). Proved: existence transports both ways " ++
        "(nonempty_stageConstructionTrace_iff_definition31Data) and the " ++
        "round trip is the identity " ++
        "(stageConstructionTrace_transport_roundtrip). Verdict: transport " ++
        "is exact but adds no supply; the two carriers carry the same " ++
        "fields (18 fields; the trace partition slot is forced by " ++
        "partition_alignment), so a trace-side construction is the same " ++
        "work as a contract-side construction. r4 blocked at the same " ++
        "clause supply as r1. Reduced form: logical transport only; no " ++
        "source reduction is constructed here."
    dependsOn :=
      [ "IUT-III.theorem-3.11-output.source-input-residual",
        "IUT-I.definition31-carrier-consolidation" ] }

/-- r5 card: the family-law layer does not supply the theater system. -/
def sourceProcessionFamilyLawSupplyCard : Obligation :=
  { id :=
      "IUT-III.theorem-3.11-output.source-input-residual.procession-family-law-supply"
    source :=
      "IUT I, Theorem A preamble (line 736); Corollary 3.8 (line 5039)"
    status := VerificationStatus.interface
    note :=
      "r5 of the procession-residual attack (stage C). The family layer " ++
        "(SourceHodgeTheaterFamily.lean:23-46) supplies index, injective " ++
        "theater into HodgeTheater, HodgeTheaterLink refl/symm/trans laws " ++
        "and the permutation naturality square; its own header records " ++
        "the open obligation IUT-I.hodge-theater-family-source-reduction " ++
        "(construction of a family from Definition 3.1 data). The " ++
        "SourceHodgeTheaterSystem contract (SourceHodgeTheaterBridge:40) " ++
        "additionally needs source : SourceDefinition31Data plus " ++
        "qParameter/scale with their constancy laws, absent from the " ++
        "family layer, and its link slot asks for endo-maps on " ++
        "theaterCarrier, not HodgeTheaterLink bundles (different shapes; " ++
        "no conversion is assumed). Verdict: the family laws cannot " ++
        "replace the source datum S; r5 blocked at S plus q/scale supply. " ++
        "Reduced form: supply verdict only."
    dependsOn :=
      [ "IUT-III.theorem-3.11-output.source-input-residual",
        "IUT-I.hodge-theater-family-source-reduction" ] }

/-- Updated residual status: the procession residual reduces to the
source datum `S` alone, with the canonical construction explicitly
labelled degenerate. -/
def sourceProcessionResidualRevision : Obligation :=
  { id :=
      "IUT-III.theorem-3.11-output.source-input-residual.procession-canonical-reduction"
    source :=
      "IUT III, Theorem 3.11, (i) (III:9164-9175); IUT I, Definition 3.1"
    status := VerificationStatus.conditional
    note :=
      "Updated status of the P entry of " ++
        "IUT-III.theorem-3.11-output.source-input-residual (stage C). " ++
        "Original routes preserved (report section 10): r1 direct " ++
        "construction - no tree supplier of SourceDefinition31Data; r2 via " ++
        "the Completion package - circular (Input is a field, " ++
        "SourceRealizationLifting:43-57); r3 via the finite Q(i)-at-5 " ++
        "carrier - no morphism to the source-world types. Added: r4 " ++
        "(procession-trace-bridge card: exact transport, no supply gain) " ++
        "and r5 (procession-family-law-supply card: source datum and " ++
        "q/scale absent from the family layer). Positive reduction (this " ++
        "file): from S and a base point, canonicalSourceHodgeTheaterSystem " ++
        "-> sourceLGPProcessionOfDefinition31Data -> item 19's composition " ++
        "yields Theorem311Source.Input (sourceInputOfDefinition31Data, " ++
        "sourceInput_nonempty_of_definition31Data). Residual is now the " ++
        "single object S = SourceDefinition31Data; the construction is " ++
        "degenerate (identity/constants, no arithmetic content); the " ++
        "D3-D11 source gates remain open (no degenerate selection is used " ++
        "to close them); not the general Theorem 3.11 form."
    dependsOn :=
      [ "IUT-III.theorem-3.11-output.source-input-residual.packet-carrier-cards",
        "IUT-III.theorem-3.11-output.source-input-residual.procession-trace-bridge",
        "IUT-III.theorem-3.11-output.source-input-residual.procession-family-law-supply" ] }

end LeanFormal.IUT.Audit
