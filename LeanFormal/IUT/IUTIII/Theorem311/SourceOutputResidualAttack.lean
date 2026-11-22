import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteOutputLawBundleVerticalWiring
import LeanFormal.IUT.Audit.Status
import Mathlib.Tactic

/-!
# Residual attack on the item-17 source-input card: canonical packet carrier

Task (2026-10-16, follow-up to `SourceFiniteOutputLawBundleVerticalWiring`):
attack the residual of `theorem311SourceInputResidual` card by card, and
record the packet-carrier specification of the output-side route.  After the
vertical wiring the residual is: the procession `P`, the packet `Q`, and the
three packet-consistency cards N1/N2/A1
(`K1K2BoundaryReduction.nonarchimedeanImageInclusion`,
`.ind3ImageWellDefined`, `.archimedeanTargetLift`).

Findings recorded here:

* `Q` (packet carrier): constructible as a distinguished degenerate test
  packet `canonicalPacketRealization` for an arbitrary given `P`: `PUnit`
  carrier, trivial log-volume and determinant, full `possibleImage`.
* N1/N2/A1: proved for that test packet (`canonicalPacket_imageInclusion`,
  `canonicalPacket_ind3WellDefined`, `canonicalPacket_targetLift`), hence
  jointly satisfiable (`packetCards_jointlySatisfiable`).  For a general `Q`
  the three cards remain conditional; the failure models are documented in
  `K1K2BoundaryReduction.lean` (IUTII/Kummer).
* Consequently `SourceTheorem311Realization` and `Theorem311Source.Input`
  are constructible from the procession `P` alone
  (`sourceTheorem311RealizationOfProcession`, `sourceInputOfProcession`):
  the packet-side residual is absorbed by the test packet.
* `P` (procession): still parked.  `SourceLGPProcession` requires a
  `SourceHodgeTheaterSystem` (`SourceHodgeTheaterBridge.lean:40,158`), which
  requires `SourceDefinition31Data`; no tree declaration constructs it
  outside the completion context.  Named source gap: the IUT-I
  hodge-theater family supply (`IUT-I.hodge-theater-family-source-reduction`).

Honest labels (reduced forms):

* `canonicalPacketRealization` is degenerate: constants `0`/`1`, full image
  set, `PUnit` carrier.  It carries no arithmetic content; it shows only
  that the card set is satisfiable and that no further packet-side
  arithmetic is needed to construct `Input` from `P`.
* `sourceInputOfProcession` is a conditional construction: it assumes `P`.
  Nothing here constructs `P`, and nothing here claims the general
  Theorem 3.11 statement.
* The cards N1/N2/A1 are reproduced from `K1K2BoundaryReduction` (cited
  there to IUT III Proposition 3.5 (ii) and Theorem 3.11 (ii) (Ind3)); the
  cards are reduced forms, not the original statements.

Corpus anchors: IUT III, Theorem 3.11 opening (III:9151-9163), (i)
procession of D-prime-strips (III:9164-9175), (ii) log-volume/Ind3
directions (III:9176-9191).

Audit records in namespace `LeanFormal.IUT.Audit` at the end register the
packet-carrier card reduction (stage A) and the packet-carrier
specification (stage B).
-/

namespace LeanFormal.IUT

noncomputable section

universe u v w

/-! Residual attack namespace: the canonical test packet, the three
packet-consistency cards on it, and the composition into the frozen
`SourceTheorem311Realization` / `Theorem311Source.Input`. -/
namespace SourceOutputAttack

open Theorem311Source
open Theorem311Source.SourceHodgeTheaterBridge
open Theorem311Source.SourceDependencyChain

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]

/-! ## 1. The canonical test packet -/

/-- The canonical test packet over an arbitrary given procession `P`:
`PUnit` carrier, distinguished point `unit`, log-volume `0`, determinant
`1`, possible image the full set of reals.  All frozen packet laws hold
definitionally (`rfl`/`le_rfl`) or by `Real.log_one`.  Degenerate by
construction: the packet laws do not relate the packet data to the
arithmetic of `P`, so this packet carries no arithmetic content. -/
def canonicalPacketRealization (P : SourceLGPProcession.{u, v} l Label Choice) :
    SourcePacketRealization.{u, v, w} P where
  carrier := fun _ => PUnit.{w+1}
  distinguished := fun _ => PUnit.unit
  logVolume := fun _ => 0
  determinant := fun _ => 1
  determinant_positive := fun _ => zero_lt_one
  log_determinant := fun _ => Real.log_one
  possibleImage := fun _ => Set.univ
  possibleImage_nonempty := fun _ => ⟨(0 : Real), Set.mem_univ 0⟩
  ind1_volume := fun _ _ => rfl
  ind2_volume := fun _ _ => rfl
  ind3_volume := fun _ _ => le_rfl
  ind1_determinant := fun _ _ => rfl
  ind2_determinant := fun _ _ => rfl
  ind3_determinant := fun _ _ => le_rfl
  image_ind1 := fun _ _ => rfl
  image_ind2 := fun _ _ => rfl
  image_ind3 := fun _ _ z _ => ⟨z, Set.mem_univ z, le_rfl⟩

/-! ## 2. The three packet-consistency cards on the test packet -/

/-- Card N1 (`nonarchimedeanImageInclusion`) holds for the canonical test
packet: with the full possible image, the required inclusion is the
degenerate subset relation of `Set.univ`. -/
theorem canonicalPacket_imageInclusion
    (P : SourceLGPProcession.{u, v} l Label Choice) :
    K1K2BoundaryReduction.nonarchimedeanImageInclusion P
      (canonicalPacketRealization P) :=
  fun _ _ => Set.subset_univ _

/-- Card N2 (`ind3ImageWellDefined`) holds for the canonical test packet:
both compared target images are the full set. -/
theorem canonicalPacket_ind3WellDefined
    (P : SourceLGPProcession.{u, v} l Label Choice) :
    K1K2BoundaryReduction.ind3ImageWellDefined P
      (canonicalPacketRealization P) :=
  fun _ _ _ _ => rfl

/-- Card A1 (`archimedeanTargetLift`) holds for the canonical test packet:
the lift takes the point itself, with `z ≤ z`. -/
theorem canonicalPacket_targetLift
    (P : SourceLGPProcession.{u, v} l Label Choice) :
    K1K2BoundaryReduction.archimedeanTargetLift P
      (canonicalPacketRealization P) :=
  fun _ _ z _ => ⟨z, Set.mem_univ z, le_rfl⟩

/-- The three packet-consistency cards are jointly satisfiable over any
given procession `P`, with the canonical test packet as witness.  This
does not make the cards true for an arbitrary packet; it shows that the
card set is consistent and that the packet-side obstruction is not
arithmetic in nature at this interface. -/
theorem packetCards_jointlySatisfiable
    (P : SourceLGPProcession.{u, v} l Label Choice) :
    ∃ Q : SourcePacketRealization.{u, v, w} P,
      K1K2BoundaryReduction.nonarchimedeanImageInclusion P Q ∧
        K1K2BoundaryReduction.ind3ImageWellDefined P Q ∧
          K1K2BoundaryReduction.archimedeanTargetLift P Q :=
  ⟨canonicalPacketRealization P, canonicalPacket_imageInclusion P,
    canonicalPacket_ind3WellDefined P, canonicalPacket_targetLift P⟩

/-! ## 3. Composition into the frozen realization and input -/

/-- The vertical element of the five-element tuple for the canonical test
packet, through the frozen card route
(`SourceOutputWiring.sourceVerticalRealizationOfImageCards`). -/
def sourceVerticalRealizationOfCanonicalPacket
    (P : SourceLGPProcession.{u, v} l Label Choice) :
    SourceVerticalRealization.{u, v, w} P (canonicalPacketRealization P) :=
  SourceOutputWiring.sourceVerticalRealizationOfImageCards P
    (canonicalPacketRealization P) (canonicalPacket_imageInclusion P)
    (canonicalPacket_ind3WellDefined P) (canonicalPacket_targetLift P)

/-- The five-element realization of the frozen output route, constructed
from the procession `P` alone: packet by the canonical test packet,
vertical by the card route, evaluation and family slots by the canonical
identity data, labelled count one. -/
def sourceTheorem311RealizationOfProcession
    (P : SourceLGPProcession.{u, v} l Label Choice) :
    SourceTheorem311Realization.{u, v, w} l Label Choice where
  procession := P
  packet := canonicalPacketRealization P
  vertical := sourceVerticalRealizationOfCanonicalPacket P
  evaluation := SourceOutputWiring.sourceEvaluationBridgeOfVertical P
    (canonicalPacketRealization P)
    (sourceVerticalRealizationOfCanonicalPacket P)
  genericFamily := SourceOutputWiring.identityTheaterFamily Choice
  labelledCount := 1
  labelledCount_pos := Nat.one_pos

/-- The frozen source-input package, constructed from the procession `P`
alone through the canonical test packet.  Conditional construction: `P`
itself remains the parked source residual. -/
def sourceInputOfProcession
    (P : SourceLGPProcession.{u, v} l Label Choice) :
    Theorem311Source.Input.{u, v, w} Label Choice :=
  (sourceTheorem311RealizationOfProcession P).input

/-- The frozen source-input package is nonempty for any given procession. -/
theorem sourceInput_nonempty_of_procession
    (P : SourceLGPProcession.{u, v} l Label Choice) :
    Nonempty (Theorem311Source.Input.{u, v, w} Label Choice) :=
  ⟨sourceInputOfProcession P⟩

end SourceOutputAttack

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Packet-carrier card reduction (stage A of the item-17 residual attack):
card-by-card status of the residual `P`, `Q`, N1/N2/A1, with `Q` provided
by the canonical test packet and N1/N2/A1 proved on it. -/
def sourcePacketCarrierCardsReduction : Obligation :=
  { id := "IUT-III.theorem-3.11-output.source-input-residual.packet-carrier-cards"
    source := "IUT III, Theorem 3.11, (ii) (Ind3); Proposition 3.5, (ii)"
    status := VerificationStatus.testCarrier
    note :=
      "Stage A of the item-17 residual attack. Card status: " ++
        "(1) P (procession): parked - needs SourceHodgeTheaterSystem " ++
        "(SourceDefinition31Data plus theater index/carrier/q/scale/Perm; " ++
        "SourceHodgeTheaterBridge:40,158); no tree construction outside " ++
        "the completion context; named source gap " ++
        "IUT-I.hodge-theater-family-source-reduction. " ++
        "(2) Q (packet): proved - canonical degenerate test packet " ++
        "canonicalPacketRealization (PUnit carrier, zero log-volume, unit " ++
        "determinant, full possible image). (3) N1/N2/A1: proved for the " ++
        "test packet (canonicalPacket_imageInclusion, " ++
        "canonicalPacket_ind3WellDefined, canonicalPacket_targetLift); " ++
        "jointly satisfiable (packetCards_jointlySatisfiable); a general Q " ++
        "remains conditional (failure models in K1K2BoundaryReduction). " ++
        "Consequence: Theorem311Source.Input is constructible from P alone " ++
        "(sourceTheorem311RealizationOfProcession, sourceInputOfProcession). " ++
        "Reduced form: satisfiability witness only; no arithmetic content; " ++
        "not the original statements."
    dependsOn :=
      [ "IUT-III.theorem-3.11-output.source-input-residual",
        "IUT-III.concrete-source-output-law-bundle.vertical-wiring",
        "IUT-II.vertical-log-kummer" ] }

/-- Packet-carrier specification (stage B): the field book of
`SourcePacketRealization` beyond the ray presentation, with consumers. -/
def sourcePacketCarrierSpec : Obligation :=
  { id := "IUT-III.theorem-3.11-output.source-input-residual.packet-carrier-spec"
    source := "IUT III, Theorem 3.11, opening (III:9151-9163), (ii) (III:9176-9191)"
    status := VerificationStatus.interface
    note :=
      "Stage B field book of the packet/log-volume carrier " ++
        "SourcePacketRealization. Fields (SourceHodgeTheaterBridge:339-360): " ++
        "carrier; distinguished; logVolume; determinant with positivity and " ++
        "the log law; nonempty possibleImage; ind1-3 volume laws; ind1-3 " ++
        "determinant laws; image_ind1/ind2 equalities and image_ind3 upper " ++
        "bound (no membership). Consumers: profile (:370) and localPacket " ++
        "(:381) project into Theorem311Source.Input (:928); possibleImage " ++
        "feeds the three K1 cards and the vertical element " ++
        "(K1K2BoundaryReduction:142-197,368); LogShellRayPresentation " ++
        "(SourceK1K2Realization:107) characterizes possibleImage by a ray " ++
        "system but does not construct the carrier. The finite Q(i)-at-5 " ++
        "carrier (SourceFiniteOutput:233) is a parallel test carrier with " ++
        "no morphism to SourcePacketRealization. Spec bookkeeping only; " ++
        "proves nothing about the actual source packet."
    dependsOn :=
      [ "IUT-III.theorem-3.11-output.source-input-residual",
        "IUT-III.concrete-source-output-law-bundle.vertical-wiring",
        "IUT-I-II.prime-strips-frobenioids" ] }

end LeanFormal.IUT.Audit
