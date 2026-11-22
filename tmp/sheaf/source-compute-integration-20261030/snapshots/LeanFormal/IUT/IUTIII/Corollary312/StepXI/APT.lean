import LeanFormal.IUT.IUTIII.Corollary312.Obligations
import LeanFormal.IUT.IUTIII.Theorem311.SourceMultiradialTwoActionEquivalence
import LeanFormal.IUT.IUTIII.Theorem311.SourceArithmeticHolomorphicLanding

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Algorithmic parallel transport (APT) with invariants (reduced interface)

Reduced source-level interface of the "algorithmic parallel transport" (APT)
property of IUT III, Remark 3.11.1, (iv), used in Corollary 3.12, Step
(xi-b)/(xi-c), together with its assembly into the (APT) slot of the north-wall
three-card contract.  This file is the APT-side implementation point of the
obligation `IUT-III.APT` (`Corollary312/Obligations.lean:19-24`,
`dependsOn = IUT-III.SHE + IUT-II.vertical-log-kummer`).

## Original (paper) route

* IUT III, Remark 3.11.1, (iv) (pagewise `:9923-9946`): the SHE property of
  (iii) "may be thought of as a sort of 'parallel transport' mechanism for the
  Theta-pilot object ... up to certain mild indeterminacies, from the
  [arithmetic holomorphic structure ... in the] domain of the Theta-link to the
  [arithmetic holomorphic structure ... in the] codomain of the Theta-link".
  The bullet `(Algorithmic parallel transport (APT))` (`:9931-9938`) is the
  content frozen here: the mechanism "does not consist of a simple instance of
  transport of some set-theoretic region ... via some set-theoretic function.
  Rather, it consists of a construction algorithm that is simultaneously
  valid/executable/well-defined with respect to the arithmetic holomorphic
  structures in the domain and codomain of the Theta-link".  Theta functions
  and theta values appear only as hidden internal structures ((HIS),
  `:9947-9958`).
* IUT III, Corollary 3.12, Step (xi-b) (focused extract
  `IUTIII_Theorem311_pp153-159_Corollary312_pp173-186.plain.txt:1007-1044`,
  PDF pp. 181-182): under the qualitative reading one keeps only the (IPL),
  (SHE) and (APT) properties of Remark 3.11.1, (iii), (iv), (v) (the
  three-property list at `plain.txt:1032-1034`); the algorithm is read as
  ""some" algorithm that transforms a certain type of input data into a
  certain type of output data and, moreover, satisfies certain properties
  (IPL) and (SHE)" (`plain.txt:1040-1044`).  Step (xi-c) (`plain.txt:1045-1066`)
  is the summary of the (IPL)+(SHE) reading; APT frames this output-data
  construction as an algorithmic (not set-theoretic) transport.
* Attribution note: `Corollary312/Obligations.lean:19-24` cites APT as "Step
  (xi-c)"; the definition place is Remark 3.11.1, (iv), and its listing in the
  proof is Step (xi-b) (DSH-F report section 1.1).  This module freezes the
  corrected attribution.

## Reduced route (deviations)

R1. Structures. The "arithmetic holomorphic structures in the domain and
    codomain of the Theta-link" are reduced to two multiradial presentations
    (Cards MP/MA of `SourceMultiradialTwoActionEquivalence.lean`); no
    Theta-plus-minus-ellNF-Hodge-theater carrier is constructed and no
    identification of the abstract outputs with theater data is asserted.
R2. Simultaneity. "Simultaneously valid/executable/well-defined with respect
    to" both structures is reduced to one transport record over two algorithm
    instances sharing the (Ind2) action carrier (the canonical Ism copies,
    API-4 R6), whose comparison preserves both actions; no operation-level
    scheme-theoretic semantics is modeled.
R3. Algorithmic nature. The negative clause ("not a set-theoretic region
    transport") is NOT formalized: no negative statement and no `True` marker
    is frozen.  The positive reduced content is: the transport is the
    action-preserving comparison of the two algorithm instances and descends
    to their generated quotients (Section 1).
R4. Invariants. The invariants carried are exactly the (Ind1)/(Ind2)
    equivariance of the comparison (API-4) and the descended quotient
    equivalence.  The (Ind3) upper-semi/log-Kummer portion of Theorem 3.11,
    (ii) is out of scope (API-4 R5, separate vertical log-Kummer contract);
    "mild indeterminacies" are not measured.
R5. (HIS). The qualitative forgetting of theta functions/values is not
    modeled.
R6. Times-mu layer. The transport lives over the F-prime-strip/abstract
    presentation layer; the times-mu component (DSH-F API-1) is not
    constructed.
R7. SHE coupling. The record carries the SHE landing datum
    `SourceLocalizationExpressible S Output'` as a field: the SHE card in its
    general (still open) form.  The source construction consumes the named
    card `IUT-III.source-SHE-landing-evidence`; the number-field completion
    instance of `SourceArithmeticHolomorphicLanding.lean` (Section 6 there) is
    a special case and does NOT discharge the general card.  No output carrier
    is identified with the q-pilot object.
R8. Adjacency. The intended source instance of the transport runs along
    adjacent columns `(n, n+1)` of the log-theta-lattice; adjacency is not
    enforced as a field, and no adjacent-column procession isomorphism is
    constructed (DSH-F API-2 remains open).

## Named source cards (not constructed here)

* Card APT: `SourceAlgorithmicParallelTransport` (two algorithm instances
  with the action-preserving comparison and the SHE landing datum).
* Consumed cards: `IUT-III.source-SHE-landing-evidence` (general form, R7);
  `IUT-II.vertical-log-kummer` (repo counterpart: the K1/K2 boundary
  interfaces `SourceK1K2Construction.lean:666-689`, still explicit source
  obligations).

## Proved here

The nonemptiness characterizations of the transport record -- general, and
reflexive (`nonempty_iff_self`: a transport from an algorithm to itself exists
exactly when the general SHE landing datum exists, so the record is sharp on
its SHE dependence and cannot be inhabited without it); generated-relation
preservation and the descended quotient equivalence (reused from the proved
API-4 descent); composition of transports; the (APT) slot assembly record with
evidence transport into `StepXIContract.apt`; and the two conditional
instantiation-site assemblies, whose slot identification is `rfl`.

## Not claimed here

The actual source algorithms and their (Ind1)/(Ind2) actions over the actual
output data, the actual SHE landing evidence, the vertical log-Kummer
construction, adjacent-column procession isomorphisms, the times-mu layer, the
(Ind3) content, and any numerical or IPL/SHE conclusion.

## Consumers

* The (APT) slot of the north-wall three-card contract: `StepXIContract.apt`
  (`Corollary312/StepXI/Contract.lean:39`; evidence field `apt_evidence` at
  `Contract.lean:42`; `WallObligation.apt` at `Contract.lean:26`; the
  contract-construction obligation lists `IUT-III.APT` at `Contract.lean:76`).
  Instantiation points `ContractSourceReduction.lean:212-213`
  (`finiteLinkEvidenceOfHullTarget`, the `apt`/`apt_evidence` arguments) and
  `ContractSourceReduction.lean:270-271`
  (`StepXIContract.ofAbsoluteDegreeNormalizedSignedLog`); parametric carrier
  fields `ParametricStepXI.lean:37`/`:40` (`StepXIInput.apt`/`apt_evidence`).
  See Section 3 for `SourceAPTSlotAssembly`.
* The obligation `IUT-III.APT` itself (`Corollary312/Obligations.lean:19-24`);
  this module's Audit records track the reduced interface and the named
  supply card.

## Paper locations

IUT III, Remark 3.11.1: (iii) pagewise `:9843-9907` (IPL `:9850-9865`; SHE
`:9890-9907`); (iv) pagewise `:9923-9946` ((APT) `:9931-9938`; (HIS)
`:9947-9958`); (v) pagewise `:9982-10000`.  Corollary 3.12, Step (xi-b):
focused extract `:1007-1044` (three-property list `:1032-1034`); Step (xi-c):
`:1045-1066`.  Framework references: [IUTchII] Remarks 1.7.1, 1.9.2
(crystals/connections analogy, cited in (iv)).
-/

namespace LeanFormal.IUT

universe uG uG' uG'' uG₂ uv ua upi umon ui uOut₁ uOut₂ uOut₃

namespace Theorem311Source
/-! ## 1. The reduced algorithmic parallel transport (Card APT) -/

section Transport

variable {l : PrimeGeFive}
variable {V : Type uv}
variable {G₁ : Type uG} [Group G₁] {G₁' : Type uG'} [Group G₁']
variable {G₂ : Type uG₂} [Group G₂]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V} {n n' : Int}
variable {Output₁ : Type uOut₁} {Output₂ : Type uOut₂}

/-- Card APT: the reduced algorithmic parallel transport between two
multiradial algorithm instances of Theorem 3.11 (the domain and codomain sides
of the Theta-link; the intended source instance is along adjacent columns,
R8).  The comparison is the "simultaneously valid/executable/well-defined"
surface (R2), and its preservation fields are the (Ind1)/(Ind2) invariants
(R4); the landing datum is the SHE card in its general, still open form (R7). -/
structure SourceAlgorithmicParallelTransport
    (S : SourceOneColumnArithmeticHolomorphicStructure V)
    (A : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output₁)
    (A' : SourceTheorem311MultiradialAlgorithm G₁' G₂ I n' Output₂) where
  /-- the action-preserving comparison of the two algorithm instances: the
  (Ind1)/(Ind2) invariants of the transport (R4) -/
  comparison : SourceTheorem311TwoActionEquivalence A A'
  /-- the SHE landing datum of the codomain-side output data: the general SHE
  card `IUT-III.source-SHE-landing-evidence` (R7) -/
  landing : SourceLocalizationExpressible S Output₂

namespace SourceAlgorithmicParallelTransport

variable {S : SourceOneColumnArithmeticHolomorphicStructure V}
variable {A : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output₁}
variable {A' : SourceTheorem311MultiradialAlgorithm G₁' G₂ I n' Output₂}

/-- The descended quotient equivalence of the transport: the two-action
equivalence of the comparison descends to the quotients of the outputs by the
generated relations (reused from the proved API-4 descent). -/
def quotientEquiv (D : SourceAlgorithmicParallelTransport S A A') :
    Quotient (twoActionSetoid A) ≃ Quotient (twoActionSetoid A') :=
  D.comparison.quotientEquiv

/-- Computation law for the descended quotient equivalence. -/
@[simp] theorem quotientEquiv_mk (D : SourceAlgorithmicParallelTransport S A A')
    (o : Output₁) :
    D.quotientEquiv (Quotient.mk (twoActionSetoid A) o) =
      Quotient.mk (twoActionSetoid A') (D.comparison.outputEquiv o) :=
  D.comparison.quotientEquiv_mk o

/-- The transport preserves and reflects the generated relations: two source
outputs are in the same (Ind1)/(Ind2) orbit class precisely when their
transported images are. -/
theorem twoActionGeneratedRel_iff (D : SourceAlgorithmicParallelTransport S A A')
    {o₁ o₂ : Output₁} :
    TwoActionGeneratedRel A o₁ o₂ ↔
      TwoActionGeneratedRel A' (D.comparison.outputEquiv o₁)
        (D.comparison.outputEquiv o₂) :=
  ⟨fun h => D.comparison.twoActionGeneratedRel_map h,
    fun h => by
      have h' := D.comparison.twoActionGeneratedRel_map_symm h
      simpa using h'⟩

/-- Gate/characterization: a transport exists exactly when a two-action
equivalence of the two instances and the SHE landing datum exist; the record
adds no further field. -/
theorem nonempty_iff :
    Nonempty (SourceAlgorithmicParallelTransport S A A') ↔
      Nonempty (SourceTheorem311TwoActionEquivalence A A') ∧
        SourceLocalizationExpressible S Output₂ :=
  ⟨fun ⟨D⟩ => ⟨⟨D.comparison⟩, D.landing⟩,
    fun ⟨⟨c⟩, h⟩ => ⟨{ comparison := c, landing := h }⟩⟩

/-- The reflexive transport of an algorithm instance over its own landing
datum (the trivial-comparison gate instance; see `nonempty_iff_self`). -/
def reflexive (A : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output₁)
    (landing : SourceLocalizationExpressible S Output₁) :
    SourceAlgorithmicParallelTransport S A A where
  comparison := SourceTheorem311TwoActionEquivalence.refl A
  landing := landing

/-- Sharp characterization of the reflexive case: a transport from an
algorithm instance to itself exists exactly when the general SHE landing datum
exists.  This is the reduced form of "APT is a reading of the SHE mechanism"
(Remark 3.11.1, (iv)): the record cannot be inhabited without the SHE card. -/
theorem nonempty_iff_self
    (A : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output₁) :
    Nonempty (SourceAlgorithmicParallelTransport S A A) ↔
      SourceLocalizationExpressible S Output₁ :=
  ⟨fun ⟨D⟩ => D.landing, fun h => ⟨reflexive A h⟩⟩

end SourceAlgorithmicParallelTransport

end Transport

/-! ## 2. Composition of transports -/

section Composition

variable {l : PrimeGeFive}
variable {V : Type uv}
variable {G₁ : Type uG} [Group G₁] {G₁' : Type uG'} [Group G₁']
variable {G₁'' : Type uG''} [Group G₁'']
variable {G₂ : Type uG₂} [Group G₂]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V} {n n' n'' : Int}
variable {Output₁ : Type uOut₁} {Output₂ : Type uOut₂} {Output₃ : Type uOut₃}
variable {S : SourceOneColumnArithmeticHolomorphicStructure V}
variable {A : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output₁}
variable {A' : SourceTheorem311MultiradialAlgorithm G₁' G₂ I n' Output₂}
variable {A'' : SourceTheorem311MultiradialAlgorithm G₁'' G₂ I n'' Output₃}

/-- Composition of transports through a common algorithm instance.  The
resulting comparison is the composition of the two comparisons (group
identification and output equivalence) and carries the final landing datum;
for adjacent-column instances this is the reduced form of stepping twice along
the log-theta-lattice.  Adjacency and the paper's procession isomorphisms are
not constructed (R8). -/
def SourceAlgorithmicParallelTransport.trans
    (D₁ : SourceAlgorithmicParallelTransport S A A')
    (D₂ : SourceAlgorithmicParallelTransport S A' A'') :
    SourceAlgorithmicParallelTransport S A A'' where
  comparison :=
    { ind1GroupEquiv :=
        D₁.comparison.ind1GroupEquiv.trans D₂.comparison.ind1GroupEquiv
      outputEquiv :=
        D₁.comparison.outputEquiv.trans D₂.comparison.outputEquiv
      preserves_ind1 := by
        intro g o
        change D₂.comparison.outputEquiv
              (D₁.comparison.outputEquiv (A.ind1Action g o)) =
            A''.ind1Action
              (D₂.comparison.ind1GroupEquiv
                (D₁.comparison.ind1GroupEquiv g))
              (D₂.comparison.outputEquiv
                (D₁.comparison.outputEquiv o))
        rw [D₁.comparison.preserves_ind1, D₂.comparison.preserves_ind1]
      preserves_ind2 := by
        intro g o
        change D₂.comparison.outputEquiv
              (D₁.comparison.outputEquiv (A.ind2Action g o)) =
            A''.ind2Action g
              (D₂.comparison.outputEquiv
                (D₁.comparison.outputEquiv o))
        rw [D₁.comparison.preserves_ind2, D₂.comparison.preserves_ind2] }
  landing := D₂.landing

end Composition
/-! ## 3. The (APT) slot assembly into the north-wall contract -/

section SlotAssembly

variable {l : PrimeGeFive}
variable {V : Type uv}
variable {G₁ : Type uG} [Group G₁] {G₁' : Type uG'} [Group G₁']
variable {G₂ : Type uG₂} [Group G₂]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V} {n n' : Int}
variable {Output₁ : Type uOut₁} {Output₂ : Type uOut₂}
variable {S : SourceOneColumnArithmeticHolomorphicStructure V}
variable {A : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output₁}
variable {A' : SourceTheorem311MultiradialAlgorithm G₁' G₂ I n' Output₂}

/-- The proposition carried by the (APT) slot of the north-wall contract for a
given pair of algorithm instances: inhabitation of the reduced transport
record.  This is the frozen content of `apt` at the instantiation sites. -/
def SourceAPTStatement (S : SourceOneColumnArithmeticHolomorphicStructure V)
    (A : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output₁)
    (A' : SourceTheorem311MultiradialAlgorithm G₁' G₂ I n' Output₂) : Prop :=
  Nonempty (SourceAlgorithmicParallelTransport S A A')

/-- Minimal assembly point wiring the APT statement into the (APT) slot of the
north-wall three-card contract (`Corollary312/StepXI/Contract.lean`).

Consumers (file:line): the slot declaration `StepXIContract.apt` at
`Contract.lean:39` and its evidence field `apt_evidence : apt` at
`Contract.lean:42` (the contract-construction obligation lists `IUT-III.APT`
at `Contract.lean:76`); instantiation sites `ContractSourceReduction.lean:212-213`
(`finiteLinkEvidenceOfHullTarget`, the `apt`/`apt_evidence` arguments) and
`ContractSourceReduction.lean:270-271`
(`StepXIContract.ofAbsoluteDegreeNormalizedSignedLog`); parametric carrier
fields `ParametricStepXI.lean:37`/`:40` (`StepXIInput.apt`/`apt_evidence`).

The contract is NOT constructed here: the signed quantities, the (IPL)/(SHE)
propositions with their evidence, and the two real comparisons remain caller
obligations, and no slot is closed by `True` or by any trivial proposition.
Frozen here is only the identification: the assembled contract carries
`SourceAPTStatement S A A'` in its (APT) slot, so a caller building the
contract with `apt := SourceAPTStatement S A A'` inhabits `slot_identifies` by
`rfl` and obtains the slot evidence from APT evidence via `aptSlot_evidence`. -/
structure SourceAPTSlotAssembly
    (S : SourceOneColumnArithmeticHolomorphicStructure V)
    (A : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output₁)
    (A' : SourceTheorem311MultiradialAlgorithm G₁' G₂ I n' Output₂) where
  /-- the north-wall contract whose (APT) slot is wired -/
  contract : StepXIContract
  /-- identification of the contract (APT) slot with the APT statement
  (definitional for a contract built with `apt := SourceAPTStatement S A A'`;
  stored as data) -/
  slot_identifies : contract.apt = SourceAPTStatement S A A'

namespace SourceAPTSlotAssembly

variable {S : SourceOneColumnArithmeticHolomorphicStructure V}
variable {A : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output₁}
variable {A' : SourceTheorem311MultiradialAlgorithm G₁' G₂ I n' Output₂}

/-- Evidence transport into the (APT) slot: APT evidence for the pair
`(A, A')` over `S` is evidence for the assembled contract (APT) slot.  This is
the consumer-facing form for callers at `ContractSourceReduction.lean:212-213`
and `:270-271` that pass `apt := SourceAPTStatement S A A'`. -/
theorem aptSlot_evidence (X : SourceAPTSlotAssembly S A A')
    (h : SourceAPTStatement S A A') : X.contract.apt :=
  Eq.mp X.slot_identifies.symm h

noncomputable section

/-- Conditional assembly at the first instantiation site:
`finiteLinkEvidenceOfHullTarget` (`ContractSourceReduction.lean:210-223`) with
the (APT) slot instantiated by the APT statement, followed by
`StepXIFiniteCertificate.toContract`; on the resulting contract the (APT) slot
is definitionally the APT statement (`slot_identifies` is `rfl`).  The (IPL)
and (SHE) propositions with their evidence remain caller obligations; the
missing source input for the (APT) slot is the named card
`IUT-III.source-APT-transport-supply` (Audit below), and this assembly asserts
nothing about its availability. -/
def ofHullTargetLink {label : Type*} [Fintype label]
    (certificate : StepXIFiniteCertificate label)
    (ipl she : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (transport : SourceAPTStatement S A A') :
    SourceAPTSlotAssembly S A A' where
  contract :=
    certificate.toContract
      (finiteLinkEvidenceOfHullTarget certificate ipl she
        (SourceAPTStatement S A A') ipl_evidence she_evidence transport)
  slot_identifies := rfl

/-- Conditional assembly at the second instantiation site:
`StepXIContract.ofAbsoluteDegreeNormalizedSignedLog`
(`ContractSourceReduction.lean:259-272`) with the (APT) slot instantiated by
the APT statement; `slot_identifies` is `rfl`.  Same conditional status as
`ofHullTargetLink`. -/
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
    (ipl she : Prop) (ipl_evidence : ipl) (she_evidence : she)
    (transport : SourceAPTStatement S A A') :
    SourceAPTSlotAssembly S A A' where
  contract :=
    StepXIContract.ofAbsoluteDegreeNormalizedSignedLog selectedLowerPlaces
      parameters selected_nonempty targetSigned thetaSigned q_le_target
      target_le_theta ipl she (SourceAPTStatement S A A') ipl_evidence
      she_evidence transport
  slot_identifies := rfl

end

end SourceAPTSlotAssembly

end SlotAssembly

end Theorem311Source

namespace Audit

/-- Reduced source interface obligation (Card APT) for the algorithmic
parallel transport: the frozen record, statement, quotient descent,
composition, and the (APT) slot assembly.  Status is interface, not proved:
the actual source construction is tracked by `sourceAPTTransportSupply`. -/
def sourceAlgorithmicParallelTransport : Obligation :=
  { id := "IUT-III.source-algorithmic-parallel-transport"
    source :=
      "IUT III, Remark 3.11.1, (iv) ((APT), (HIS)); Corollary 3.12 proof, " ++
        "Step (xi-b), (xi-c) (Obligations.lean:19-24 cites Step (xi-c); the " ++
        "definition place is Remark 3.11.1, (iv), listed in Step (xi-b))"
    status := VerificationStatus.interface
    note :=
      "Reduced source interface for the algorithmic parallel transport: " ++
        "frozen record SourceAlgorithmicParallelTransport (a two-action " ++
        "equivalence between two multiradial algorithm instances -- the " ++
        "(Ind1)/(Ind2) invariants -- plus the SHE landing datum in its " ++
        "general, still open form), the statement SourceAPTStatement, the " ++
        "descended quotient equivalence, composition of transports, and the " ++
        "(APT) slot assembly SourceAPTSlotAssembly with the two conditional " ++
        "instantiation-site assemblies. Proved: nonemptiness " ++
        "characterizations (general, and reflexive -- the reflexive case is " ++
        "sharp on the SHE card), generated-relation preservation and " ++
        "reflection, and the reused API-4 quotient descent. NOT constructed: " ++
        "the actual source algorithms and their actions over the actual " ++
        "output data, the actual SHE landing evidence, the vertical " ++
        "log-Kummer construction, the adjacent-column procession " ++
        "isomorphisms, the times-mu layer, and the (Ind3) content; no " ++
        "IPL/SHE/APT conclusion and no numerical conclusion is asserted, and " ++
        "no slot is closed by True. (APT)-slot assembly identifies " ++
        "StepXIContract.apt with SourceAPTStatement and transports APT " ++
        "evidence into the slot (Contract.lean:39, 42, 76; sites " ++
        "ContractSourceReduction.lean:212-213, 270-271; " ++
        "ParametricStepXI.lean:37, 40)."
    dependsOn :=
      [ "IUT-III.source-multiradial-two-action-equivalence",
        "IUT-III.source-arithmetic-holomorphic-landing",
        "IUT-III.StepXI.contract-construction" ] }

/-- Named card for the missing source input of the (APT) slot at the two
instantiation sites: an actual inhabitant of `SourceAPTStatement` built from
the actual Theorem-3.11 output data and the vertical log-Kummer construction. -/
def sourceAPTTransportSupply : Obligation :=
  { id := "IUT-III.source-APT-transport-supply"
    source :=
      "IUT III, Remark 3.11.1, (iv); Corollary 3.12 proof, Step (xi-b), (xi-c)"
    status := VerificationStatus.pending
    note :=
      "Named card: actual source construction of an inhabitant of " ++
        "SourceAPTStatement S A A' (Card APT), consumed as the hypothesis " ++
        "transport of SourceAPTSlotAssembly.ofHullTargetLink (site " ++
        "ContractSourceReduction.lean:212-213) and " ++
        "SourceAPTSlotAssembly.ofAbsoluteDegreeNormalizedSignedLog (site " ++
        "ContractSourceReduction.lean:270-271). Minimal specification: for " ++
        "the actual Theorem-3.11 instance (I, n) and its adjacent column " ++
        "n + 1, produce the algorithm instances A, A' over the actual output " ++
        "data with their actual (Ind1)/(Ind2) actions, a two-action " ++
        "equivalence of A and A', and the SHE landing datum " ++
        "SourceLocalizationExpressible S Output' for the 1-column structure " ++
        "S. Required source mathematics: the actual algorithm realization " ++
        "over the actual outputs, the adjacent-column procession " ++
        "polymorphism (DSH-F API-2; tracked as the named card " ++
        "IUT-III.source-adjacent-column-procession-isomorphism, see " ++
        "StepXI/SourceAdjacentColumnProcessionIsomorphism.lean), the " ++
        "vertical log-Kummer construction " ++
        "(IUT-II.vertical-log-kummer; repo counterpart " ++
        "SourceK1K2Construction.lean:666-689), and the SHE landing evidence. " ++
        "Three closure routes were attempted and blocked: (a) gate closure " ++
        "over the API-4 gate algorithms -- only trivial-action instances " ++
        "exist, so this substitutes a different object; (b) discharging the " ++
        "landing field by the number-field completion instance of " ++
        "SourceArithmeticHolomorphicLanding.lean Section 6 -- a special " ++
        "case; the general SHE card remains open and is not impersonated; " ++
        "(c) the finite model FiniteAPTData " ++
        "(ConcreteFiniteRouteColumns.lean:475-532) -- wrong type (a " ++
        "shift-equivariance on a finite quotient carrier, DSH-F trap A3). " ++
        "PARKED at this named card; the two site assemblies are conditional " ++
        "on this evidence and assert nothing about its availability."
    dependsOn :=
      [ "IUT-III.APT",
        "IUT-III.source-SHE-landing-evidence",
        "IUT-II.vertical-log-kummer",
        "IUT-III.source-adjacent-column-procession-isomorphism" ] }

end Audit

end LeanFormal.IUT
