# C5 stage 1: IPL / SHE / APT shared source algorithm interface

## Template fields

- Task ID / group / owner / date: N8-C5 / group5 / multiradial / 2026-10-22.
- Goal node / SHEAF stage: C5 SourceAlgorithmCompatibility / stage 1.
- File: tmp/sheaf/n8/closure/C5-STAGE1.md (this file). No Lean file is written
  in this stage; no production file is edited; iplsheapt files are untouched.
- Integration/build owner: C10 integration owner (not this stage); build not
  applicable to this document.
- Shared interfaces/conflicts: C0-STAGE1 allowed input; C2 actual log-Kummer;
  C3 actual theta-pilot/source region; C4 stage-1 output candidate
  I.ThetaPilotPoint v. C5 does not change any shared definition.
- Continuation: after stage 1 review, a stage-2 child for the actual
  strip/Output/Choice bridge or the Remark 3.10.2 composite, assigned by the
  integration owner.
- Acceptance: statement_compiles not applicable (no Lean declaration); proof
  body not checked; this record freezes objects/quantifiers/consumers/gaps.

## Scope and explicit non-goals

C5 is the shared source-algorithm interface for the three paper properties:

- IPL: output data linked to the input prime-strip via full poly-isomorphisms
  induced by algorithm operations;
- SHE: the construction and output data are simultaneously
  valid/executable/well-defined relative to both arithmetic holomorphic
  structures;
- APT: the transport is an algorithmic construction, not a set-theoretic
  function on one region, and theta functions/values are hidden internal
  structure (HIS).

Explicit non-goals:

- C5 does NOT assert a bijection
  FPrimeStrip <-> Output <-> Choice, or a global Output0 <-> Output1
  equivalence. The paper does not require one and the repository does not have
  one.
- C5 does NOT introduce free ipl/she/apt Prop fields. The only existing slots
  are the downstream StepXIContract fields, which are consumer-side contracts,
  not C5 conclusions.
- C5 does NOT treat APT reflexivity at a single instance as the source
  statement. Reflexivity is a normal gate property; the columns/instances must
  be bound to the actual construction (OriginalInput, n/n', actual algorithm).
- C5 does NOT identify C4's candidate output I.ThetaPilotPoint v with the paper's
  full F-prime-strip output. That is C4 G4 and C5 G0.

## Allowed input versus produced data

Allowed input (C0-STAGE1.md):

~~~text
l : PrimeGeFive
V : Type
I : OriginalInput l V
~~~

Produced inside the chain:

- C1: actual place v : V and R : I.SourceImageRealization v;
- C2: actual log/Kummer data, kernel/image, Kummer arrows, K1/K2 boundary;
- C3: actual theta/q-pilot data, n : ThetaPilotCarrier l, j : SignedLabel
  l.value, source theta pilot and region;
- C4: actual source-witnessed output candidate
  U(I,n,x) with Y = I.ThetaPilotPoint v (candidate; G4 primary);
- C5: the actual algorithm record and its IPL/SHE/APT operation correspondence,
  built from the C2/C3 data and the C4 output;
- C6-C9: weights/hull/degree/q-output;
- C10: assembly.

C5 must not put any of the produced data back into the input, and must not
accept ipl/she/apt conclusions as inputs.

## C4 shared output interface

C4-STAGE1.md records, after revision:

~~~text
input I : OriginalInput l V
C1 data v : V, R : I.SourceImageRealization v
C3 data n : ThetaPilotCarrier l, j : SignedLabel l.value
output candidate Y := I.ThetaPilotPoint v
candidate C := SignedLabel l.value
candidate eval := I.sourceThetaPilotPoint v R n j
U n x := {y | exists c : C n x, eval n x c = y}
~~~

C5 consumes the same Y/C/eval only as a candidate interface. The existing APT
record uses an abstract Output type, which is not definitionally
I.ThetaPilotPoint v. C5 therefore has two separate obligations:

1. actual algorithm/output bridge: a map or type identification between the
   C4 witnessed output and the C5 algorithm Output carrier;
2. algorithm-operation compatibility: the IPL/SHE/APT laws on that bridge.

Neither is assumed. The no-dictionary gap G0 below is the root reason.

## IPL representation

Paper content: IUT III Remark 3.11.1, (iii), text anchors :9850-9878 (and the
route references in group5-STAGE1 section 1.1); Corollary 3.12 Step (xi-b).
Output data n,circ RLGP is linked to the input/coric q-pilot prime-strip by
full poly-isomorphisms induced by the algorithm operations. The link is the
composite: inverses of the first two lower horizontals, then the first vertical
Kummer arrow, then the upper horizontal evaluation arrow. The quantifier is a
permitted family, not one selected isomorphism.

Current Lean representation:

- kernel: MultiradialKernel.Core Label Choice (Theorem311/MultiradialOutputKernel);
- LinkSpan and LinkSpan.Rel (SourcePolyIsoTransportLaws:190-263);
- KummerEvaluationFactor (SourcePolyIsoTransportLaws:283):
  lower, upper : Choice -> Choice; kummer : L.mid -> L.mid;
  lower_left; upper_right;
- CardIPLTransportSupply (SourcePolyIsoTransportLaws:313):
  O1 XMu/xmuAct, O2 polyIso + act1/act2, O3 provenance routeApply,
  O4 kummerEval;
- polyIsoRel and routeRel (SourcePolyIsoTransportLaws:334, :341);
- CardIPLExchangeShape and cardIPLExchangeShape (SourcePolyIsoTransportLaws:448,
  :475);
- ReducedIplLink (SourceMultiradialIplLinkWiring:95) with target_eq,
  intermediate_compose, automorphism_compatible; no poly-isomorphism surface.

Exact IPL gap: CardIPLTransportSupply.polyIso is one equivalence
L.mid ~= L.mid, not the full permitted family; routeApply is restricted to
Ind1-like label steps; KummerEvaluationFactor is a kernel factorization, not the
actual Remark 3.10.2 four-corner composite; O1 times-mu carrier has no source
object; O4 has no relation-level Kummer transport law. These are C5 G1.

## SHE representation

Paper content: IUT III Remark 3.11.1, (iii), SHE paragraph, text anchors
:9890-9907; Corollary 3.12 Step (xi-b)/(xi-c), :10823-10898 context. Both the
construction process and the output data must be simultaneously
valid/executable/well-defined relative to the domain and codomain arithmetic
holomorphic structures; not one convenient expression per output.

Current Lean representation:

- FPrimeStrip / FPrimeStripEquiv (IUTI/HodgeTheater/PrimeStripCore:117, :166);
- SourceSimultaneousHolomorphicExpression
  (SourceSHETransportLaws:275) with domainExpression, codomainExpression,
  simultaneous;
- ofCommutingLegs, swap, transport (:299, :313, :327);
- sheStatement (:383) and sheSlot_evidence (:399);
- one-column objects SourceOneColumnArithmeticHolomorphicStructure,
  SourceArithmeticVectorBundle, SourceLocalizationExpression
  (SourceArithmeticHolomorphicLanding:155, :210, :243);
- SourceLocalizationExpressible (:292), sourceLocalizationExpressible_iff
  (:297), sourceLocalizationExpressible_of_equiv (:305).

Exact SHE gap: the two candidate SHE predicates are not cross-wired. The
landing predicate is equivalent to Nonempty Output (SourceArithmeticHolomorphic
Landing:297-300), so it adds no actual construction content. The expressions and
Kummer leg are free/opaque fields; the 1,circ column is not bound; actual source
Kummer/E1-E2 legs and times-mu/full-poly upgrades are separate obligations
(SourceSHETransportObligations:130-181). These are C5 G2.

## APT representation

Paper content: IUT III Remark 3.11.1, (iv), text anchors :9931-9938; APT/HIS
:9947-9958; Corollary 3.12 Step (xi-d)-(xi-f). The transport is an algorithm
valid/executable simultaneously relative to both structures, not a set-theoretic
region map. Theta functions/values are hidden internal structure.

Current Lean representation:

- SourceTheorem311MultiradialPresentation (SourceMultiradialTwoActionEquivalence
  :149) with output and processionAction;
- SourceTheorem311MultiradialAlgorithm (:199) with presentation, ind2Action,
  ind1_ind2_commute;
- SourceTheorem311TwoActionEquivalence (:318) with ind1GroupEquiv, outputEquiv,
  preserves_ind1, preserves_ind2;
- SourceAlgorithmicParallelTransport (APT.lean:163) with comparison and landing;
- SourceAPTStatement (APT.lean:308) := Nonempty (SourceAlgorithmicParallelTransport
  S A A');
- quotientEquiv, trans (APT.lean:183, :261);
- SourceProcessionIsomorphism (SourceAdjacentColumnProcessionIsomorphism:160)
  with levelEquiv, component, link_naturality; refl/comp at :190-236.

Exact APT gap: SourceAlgorithmicParallelTransport has only comparison + landing;
no actual algorithm steps, no operation semantics, no adjacent-column
procession isomorphism, no binding of the column indices n/n' to an actual
construction. The algorithm record's fields can be rebuilt with trivial actions;
nonempty_iff (SourceMultiradialTwoActionEquivalence:258) reduces inhabitation to
Nonempty Output. Reflexive APT at one instance is therefore a gate, not the
paper statement. These are C5 G3.

Additionally, SourceAlgorithmicParallelTransport.trans composes comparison and
output equivalences, but does not construct the paper's adjacent-column
algorithm; trans is a conditional composition of records.

## Remark 3.10.2 Kummer vertical arrow and evaluation composite

Paper content: IUT III Remark 3.10.2, text anchor :9225; Remark 3.11.1, (iii)
composite. The four-corner diagram has:
- first vertical arrow: induced Kummer isomorphism (Kummer portion);
- lower horizontals: evaluation isomorphism and tautological isomorphisms;
- upper horizontals: etale-like evaluation and natural isomorphisms;
- each lower horizontal is the conjugate of the corresponding upper horizontal
  by the vertical Kummer isomorphisms.

Current Lean representation:

- KummerEvaluationFactor (SourcePolyIsoTransportLaws:283) records only
  lower/upper/kummer and two factorization laws. This is a kernel-level
  factorization, not the actual four-corner composite.
- SourceKummerEvaluationSquare / SourceEvaluationArrow /
  SourceEvaluationUnitPortion (Theorem311/SourceKummerEvaluationArrows) record
  reduced strip/unit squares but not the actual Kummer vertical arrow composite
  with evaluation.
- SourceEvaluationUnitPortionConjugation records conjugation of a unit portion
  along two strip representatives (SourceEvaluationUnitPortionConjugation),
  still conditional on supplied Kummer arrows.

Exact composite gap: no actual source Kummer vertical arrow + actual evaluation
arrow over the same OriginalInput/column, and no theorem that their composite is
the IPL link. The kernel factorization KummerEvaluationFactor cannot be promoted
to this composite without the G0 dictionary and actual C2/C3 arrows (C5 G4).

## Consumer C7/C9/C10

- C7 SourceHolomorphicHull: consumes the actual output region U (C4) and the
  algorithm compatibility to prove common boundedness/hull containment. C5 must
  provide the actual operation correspondence; C7 cannot use a free algorithm
  record.
- C9 SourcePilotApproximation: consumes the actual q/theta source data (C3),
  IPL/SHE/APT compatibility (C5), and degree/log-volume (C8) to construct Values
  and remove hq. C5 must show the same algorithm produces the q-pilot and theta
  output values.
- C10 N8Assembly: consumes C5 as the IPL/SHE/APT provider; it must not receive
  free ipl/she/apt Props. StepXIContract is a downstream consumer type only.

Existing finite consumers (diagnostic only, not C5 output):
- StepXIContract (Contract.lean:32) has free ipl/she/apt Props with evidence
  fields;
- FiniteStepXILinkEvidence (FiniteCertificateBridge:17) has the same three free
  slots;
- linkEvidenceOfQCMP (FiniteCertificateLinkEvidenceWiring:61) leaves all three
  free; linkEvidenceOfQCMPWithIPL (:169) grounds only IPL with
  CardIPLExchangeShape, while she/apt remain free;
- SourceAPTSlotAssembly / SourceSHELandingSlotAssembly wire slots but do not
  construct source content.

These are consumer-side slots, not evidence that C5 is proved.

## Statement dependencies

- C0-STAGE1.md: allowed input l, V, I : OriginalInput l V.
- C1: v : V and R : I.SourceImageRealization v.
- C2: actual log/Kummer data and K1/K2 boundary (not yet green).
- C3: actual theta/q-pilot source data and region (not yet green).
- C4-STAGE1.md: candidate output Y = I.ThetaPilotPoint v, C/eval candidate,
  U/witness; G4 primary output-carrier gap.
- SourceImageHull: ThetaPilotPoint, sourceThetaPilotPoint, sourceThetaPilotImageAt,
  PossibleThetaPilotImageAt.
- SourceTheorem311Realization (SourceHodgeTheaterBridge:910): chain-produced
  Choice/procession/ind data.
- SourcePolyIsoTransportLaws: LinkSpan, KummerEvaluationFactor,
  CardIPLTransportSupply, polyIsoRel, CardIPLExchangeShape.
- SourceSHETransportLaws: SourceSimultaneousHolomorphicExpression, sheStatement,
  sheSlot_evidence.
- SourceArithmeticHolomorphicLanding: SourceOneColumnArithmeticHolomorphicStructure,
  SourceLocalizationExpression, SourceLocalizationExpressible.
- APT.lean: SourceAlgorithmicParallelTransport, SourceAPTStatement,
  SourceAPTSlotAssembly, trans.
- SourceMultiradialTwoActionEquivalence: Presentation, Algorithm,
  TwoActionEquivalence, quotient descent.

## Proof dependencies

- IPL: LinkSpan.Rel and polyIsoRel laws are proved conditional on
  CardIPLTransportSupply (cardIPLExchangeShape is proved from the supply), but no
  actual supply/algorithm instance is constructed.
- SHE: sheSlot_evidence is conditional on the square; landing predicate is
  equivalent to Nonempty Output; no actual source localization expression.
- APT: SourceAPTStatement is Nonempty transport; reflexive gate proof exists via
  Nonempty Output; composition trans is proved conditionally. No actual
  algorithm/adjacent-column instance.
- Remark 3.10.2: KummerEvaluationFactor is a kernel record with two laws; no
  actual source composite proof.

## Natural-language proof steps (target; not executed here)

1. Fix l, V, I : OriginalInput l V.
2. Take C1 data v,R and C3 data n,j; take C4 candidate output Y and U.
3. Build the actual algorithm instance A from the same C2/C3 data:
   actual Kummer/evaluation arrows, actual output carrier, actual Ind1/Ind2
   actions, actual column index binding n (not phantom).
4. Build a second actual instance A' for the adjacent column n' (or the
   codomain side) using the same source algorithm.
5. Define the actual output comparison A -> A' and prove the algorithm
   operation correspondence (Ind1/Ind2, Kummer/evaluation).
6. Prove IPL: the permitted family of poly-isomorphisms induced by the
   algorithm operations links A.output to the q-pilot/input prime-strip; the
   link is the inverse lower-horizontal -> vertical Kummer -> upper evaluation
   composite. Preserve the permitted-family quantifier; do not collapse to one
   isomorphism.
7. Prove SHE: the same construction and its output are simultaneously
   expressible relative to both arithmetic holomorphic structures; connect the
   strip-level square to the 1,circ localization predicate.
8. Prove APT: the transport is the actual algorithm, not a region map; prove
   operation step correspondence and composition. Reflexivity at a single
   instance is only a gate check.
9. Prove the Remark 3.10.2 composite: actual vertical Kummer arrow composed with
   actual evaluation arrow equals the IPL link on the same source data.
10. Hand the three results to C7/C9/C10 through a shared interface; no free
    ipl/she/apt Props.

Steps 3-4 and 9 are blocked by G0/G4 below.

## Reusable Mathlib / project donors

- Mathlib: Equiv.Perm, MulEquiv, Set.image/range, quotient/setoid basics;
  no heavy algebraic geometry needed for the interface.
- Project:
  - SourcePolyIsoTransportLaws (kernel LinkSpan/card supply/polyIsoRel).
  - SourceMultiradialTwoActionEquivalence (algorithm and two-action quotient).
  - APT.lean (transport record, composition, slot assembly).
  - SourceSHETransportLaws / SourceSHETransportObligations (SHE square/leg
    upgrades).
  - SourceArithmeticHolomorphicLanding (1,circ localization).
  - SourceAdjacentColumnProcessionIsomorphism (procession isomorphism).
  - SourceKummerEvaluationArrows / SourceEvaluationUnitPortionConjugation
    (reduced Kummer/evaluation squares).
  - C4-STAGE1 (output candidate and witness).
  - group5-STAGE1 (diagnosis of free slots and phantom columns; use as
    diagnostic, not as proof).

## Exact gaps

G0 (root). No actual dictionary/implementation map between the strip layer
    (FPrimeStrip), the algorithm Output layer, and the C4 Choice/witness layer.
    The tree records this twice (SourceMultiradialIplLinkWiring:41-47,
    :217-224; SourceColumnCarrierIdentification:84-88, :701-707). Consequently
    IPL/SHE/APT cannot be composed into one source statement. This is the first
    gap and is not solved by a new wiring record.

G1. IPL: CardIPLTransportSupply.polyIso is a single equivalence, not the
    permitted family; routeApply is restricted; KummerEvaluationFactor is only a
    kernel factorization; no actual source O1/O4.

G2. SHE: two uncross-wired predicates; landing predicate is Nonempty Output;
    free expressions/opaque Kummer leg; no actual 1,circ source
    localization/expression.

G3. APT: SourceAlgorithmicParallelTransport has only comparison + landing; no
    actual algorithm steps/column binding/adjacent-column procession
    isomorphism; reflexive gate is normal but not the paper statement.

G4. Remark 3.10.2 composite: no actual source Kummer vertical arrow plus actual
    evaluation arrow composite; KummerEvaluationFactor cannot substitute.

G5. Shared C4/C5 interface: C4 output is candidate I.ThetaPilotPoint v; C5
    algorithm output is an abstract Output. No bridge, and no confirmation that
    either is the paper's F-prime-strip output (C4 G4).

G6. C2/C3 actual Lean types not yet green; C0 allowed input is frozen only in
    C0-STAGE1.md, not yet a completed C0 Lean signature.

## Stop boundary and status

- This stage writes no Lean declaration and does not modify C0/C10 or production
  files.
- No free ipl/she/apt is introduced; no Strip<->Output<->Choice bijection is
  asserted; APT reflexivity is explicitly only a gate.
- Stop after this stage-1 record. The next executable action is the G0
  bridge/interface task (C1/C2/C3/C4/C5 owners) and then the Remark 3.10.2
  composite, not another wiring/canonical instance.

## Status fields

- statement_compiles: not applicable (this stage writes no Lean).
- proof_body_checked: not applicable / not run.
- kernel_closed: not applicable.
- target_accepted: not run.
- allowed input: l, V, I : OriginalInput l V.
- produced: C1 v/R, C2 log-Kummer, C3 theta/q-pilot, C4 witnessed output
  candidate, C5 algorithm/IPL/SHE/APT interface.
- consumers: C7, C9, C10.
- exact primary gap: G0 no strip/Output/Choice dictionary; C5 G1-G4 remain open.
## Label 结构更正（2026-10-23）

原文 labels 是有限集合 + arbitrary permutation automorphisms（IUT III corpus 544-570），不是 `LAdd`/Group。C5 的 `IPLRepresentation (LAdd)` 只是生产索引；共同算法表示应改用 `LabelData`/permutation action，不得把 AddGroup/Group 桥当原文实现。
