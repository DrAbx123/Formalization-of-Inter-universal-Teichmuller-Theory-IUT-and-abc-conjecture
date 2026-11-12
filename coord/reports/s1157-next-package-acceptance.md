# S1157: next-package acceptance checklist

Read: `coord/reports/source-compute-integration-20261030.md`;
`LeanFormal/IUT/IUTIII/Theorem311/Output/SourceMultiradialIplLinkWiring.lean`
(`iplAlgorithmicProvenanceCard` at :190). This is a report only; no Lean file is
changed.

## 1. First package object

File (planned, does not exist): `LeanFormal/IUT/IUTIII/Theorem311/Output/SourceOutputPrimeStripInterpretation.lean`.

Object: a `SourceRun C m` retaining the actual source generation data of one
Theorem 3.11 construction algorithm run, together with:

```text
forgetRun    : SourceRun C m -> reduced Choice
stripOfRun   : (r : SourceRun C m) -> SourceFTimesMuPrimeStrip V
diagramOfRun : (r : SourceRun C m) -> Rem3102Diagram  -- the eight strips of this run
```

and the operation-to-arrow realization:

```text
forgetRun_of_source_execution : forgetRun r = existing reduced run result
evaluation_arrow_from_source   : diagram evaluation arrow = actual evaluation arrow of r
ipl_from_source_execution      : diagram iplLink = source composite linking class of r
```

Minimum concrete chain: the four source arrows

```text
lowerEnv    : bottomEnv -> bottomGau
verticalEnv : bottomEnv -> topEnv
verticalGau : bottomGau -> topGau
upperEnv    : topEnv -> topGau      -- the actual evaluation of this run
```

and the square `lowerEnv >> verticalGau = verticalEnv >> upperEnv`, then the
adjacent Kummer square. Fill `diagram.commEnv` only after constructing the four
arrows; do not use `commEnv` itself as the proof.

## 2. Consumers (must be named in the package and checked)

- `iplAlgorithmicProvenanceCard`
  (`SourceMultiradialIplLinkWiring.lean:190`, card id
  `IUT-III.IPL.algorithmic-provenance`) -- direct consumer of the
  operation-to-arrow provenance and source link factorization bridge.
- Step-XI contract `ipl : Prop` slot
  (`LeanFormal/IUT/IUTIII/Corollary312/StepXI/Contract.lean:37-40`).
- APT site assemblies `APT.lean:370, :395` as the `ipl` hypothesis.
- `IUT-III.source-APT-transport-supply` card (APT.lean:457) -- this package
  supplies the (IPL) half only; it does not entail the (SHE) landing half.
- Existing source diagram: `SourceFTimesMuPrimeStripPolyIsomorphism.lean`
  (diagram contract :805, `iplLink` :845); reuse, do not duplicate.
- Reuse candidates from the report: `SourceH1H2Construction.fPrimeStripAt /
  fLinkAt`, `SourceFTimesMuPrimeStrip.canonical`,
  `SourceFTimesMuPrimeStripEquivalence.canonicalLift`,
  `SourceFTimesMuPrimeStripFullPolyIsomorphism.ofEquivalence/comp`.
  These supply carrier/transport only; they are not provenance.

## 3. Allowed delivery A: actual source construction

Acceptance criteria:

1. A deterministic source operation chain for one selected evaluation is
   written concretely (no arbitrary algorithm DSL, no arbitrary 8-isomorphism
   choice).
2. Four source arrows are constructed from actual source operations; the
   square commutes by an actual proof.
3. `forgetRun_of_source_execution` holds: forgetting the run gives the existing
   reduced algorithm result (forgetful, not necessarily bijective).
4. `evaluation_arrow_from_source` holds for this run's `upperEnv` and adjacent
   Kummer arrows.
5. `ipl_from_source_execution` holds: the diagram `iplLink` is the source-level
   composite, not a generic link renamed.
6. Package compiles; named consumer can use the result without extra
   assumptions; no `sorry`/`axiom`/`True`/`PUnit`.

## 4. Allowed delivery B: exact first gap

If the actual source output no longer retains enough generation data, deliver
the exact minimal missing object, not a fake construction:

- `SourceRun C m`-shaped structure/Prop with the precise fields needed
  (input, legal choices, operation outputs, strip interpretation, forget map).
- The exact first failing proposition, e.g.
  `forgetRun_of_source_execution` or `evaluation_arrow_from_source`, stated
  with actual source objects.
- A proof that the existing generic `fLinkAt`/self-conjugation/canonicalLift
  cannot be substituted for the actual evaluation arrow; record the attempted
  routes and why blocked.
- No inhabitant asserted; `dependsOn` points to the actual source-data face
  (`IUT-III.source-APT-transport-supply`, APT.lean:457) and the diagram
  contract.

Acceptance for B: the exact gap is a `Prop` (or structure with no fabricated
witness), it compiles, and the consumer card can name it as the remaining
input; `status := pending` or conditional, not closed.

## 5. Forbidden weak interfaces

- A total package whose main content is `compatible : Prop`, `isActual : Prop`,
  `holds : Prop` not tied to concrete source operations.
- Renaming a generic `fLinkAt`, self-conjugation, `canonicalLift`, or an
  arbitrary `FPrimeStripEquiv` as the actual evaluation arrow.
- Defining `upperEnv` as the composite of the other three arrows when it is
  supposed to be the actual evaluation, then claiming provenance.
- Taking an already-complete diagram with `commEnv` and using its field as the
  proof of the square.
- Putting `Q <= H`, final q membership, or the full source comparison inside
  `SourceRun`.
- Using reduced `Choice`/`Output` as if it were `SourceRun`; reverse-guessing
  a strip from a weak Choice; requiring `forgetRun` to be a bijection.
- Treating Θ-link/log-link as a ring isomorphism, or replacing the actual
  allowed image family by an arbitrary `Set X`, unit ball, or signed-j scalar
  family.
- Proving containment/inequality by silently changing it to equality, or
  introducing `True`, `PUnit`, toy carriers, or axioms.
- A package that only restates the reduced `ReducedIplLink` wiring as
  provenance; that is explicitly not an impersonation of the card.

## 6. Package order and stop condition

1. `SourceOutputPrimeStripInterpretation` (this package): source run -> strips
   -> four arrows -> square -> Kummer square -> `iplLink` provenance. Stop at
   the exact first missing source-run/arrow correspondence if it cannot be
   constructed.
2. `SourceCapsulePacketRealization`: capsule/tuple -> finite factor index ->
   source places -> completions -> actual tensor/log-shell packet.
3. `SourceHDDReadout`: actual allowed images -> hull+det/Stp5/Stp6, with
   transport equalities/bounds, not arbitrary sets.
4. `SourceSHEHDDCompatibility`: 1-column arithmetic localization, SHE/log-shift
   compatibility, readout reference compatibility.

Acceptance is per package: object actual, consumer named, statement_compiles,
proof_body_checked, kernel_closed; exact-gap packages marked conditional/pending
with the first gap named.
