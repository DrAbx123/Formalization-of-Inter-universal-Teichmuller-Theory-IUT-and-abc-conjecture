# S2380: presentation construction from cancellation data

Date: 2026-11-03. Layer: **O** (D6(c) finite-etale input).
No target change, no fake.

## Files read

- `tmp/sheaf/xif/paper/S2377StackPresentationActual.lean`
- `tmp/sheaf/xif/paper/S2089StackCancellationActual.lean`
- `tmp/sheaf/xif/paper/S2090StackCancellationObstructionActual.lean`
- `tmp/sheaf/xif/paper/S2088GMapCancellationActual.lean`
- reports `S2377-stack-presentation.md`, `S2374-stack-cancellation.md`

## Source object / domain / direction

- Source object: f's base-change presentation at point ptY.
- Inputs: g's presentation at ptY ; g, f;g's presentation at ptY, and a
  fixed-morphism postcomposition cancellation.
- Domain: original O-layer D6(c); no S2130/S2185/S2269.
- Direction: turn these inputs into a presentation of f, or record the exact
  missing construction.

## Deliverable

`tmp/sheaf/xif/paper/S2380PresentationCancellationActual.lean`

```text
EXIT=0
olean=YES
lines=78
SHA256=40EAA4E6B1FF954544792FC32004A5CE33CBF80498A89B60ED9E7DC948D758FC
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2380PresentationCancellationActual.olean
axioms: propext, Classical.choice, Quot.sound
```

## BUILT

1. `S2380PresentationInputs f g T ptY`:
   - `pointZ = ptY ; g`;
   - `gPresentation : EtaleStackBaseChangePresentation g T pointZ`;
   - `fgPresentation : EtaleStackBaseChangePresentation (f ; g) T pointZ`;
   - `cancel : Iso (a ; g) (b ; g) -> Iso a b` (local postcomposition
     cancellation).
2. `S2380ConstructFPresentation`: exact construction target
   `Inputs -> EtaleStackBaseChangePresentation f T ptY`.
3. `S2380PostcompSupply`: global fixed-morphism cancellation supply.
4. `S2380StackPresentationStatementOfConstruction`:
   construction + postcomp supply -> `S2089StackPresentationStatement`.
5. `S2380PresentationFirstMissing := Nonempty S2380ConstructFPresentation`,
   with definitional iff.

No inhabitant of the construction target is asserted.

## Exact first missing

```text
S2380ConstructFPresentation
  = forall f g T ptY,
      S2380PresentationInputs f g T ptY ->
        EtaleStackBaseChangePresentation f T ptY
```

plus a global postcomposition cancellation supply

```text
S2380PostcompSupply
  = forall g {a b}, Iso (a ; g) (b ; g) -> Iso a b
```

Together they give `S2089StackPresentationStatement`, hence stack cancellation
and the S2086 input, without S2130/S2185/S2269.

## What is not constructed

The actual presentation of f from the two given presentations is not built.
The natural missing step is exactly the local postcomposition cancellation of
comparison 2-isomorphisms. S2090 records that the global form is false in
general (constant/postcomposition information loss), so this cannot be assumed;
it is an explicit extra structure. The construction target itself is also not
inhabited.

## Relation to strong/coherent covers

Strong/coherent target covers (S2240/S2357) give per-cover presentations for
maps targeting a strong cover. They do not provide the local postcomposition
cancellation or the f-presentation for arbitrary weak covers, so they are not a
substitute for the exact first missing above.

## Consumer

`S2380StackPresentationStatementOfConstruction` ->
`S2089StackPresentationStatement` -> stack cancellation ->
`S2086CospanGMapFiniteEtaleOfStackCancellation` -> S2086 ToA assembly.

## Next executable subgoal

Either:

1. construct f's presentation from the two presentations using a genuine
   representability/faithfulness/corrected-apex theorem, not the false
   postcomposition cancellation; or
2. prove the local cancellation fails at a weak cover and record the exact
   counterexample.

No such theorem/counterexample is produced here.

## Rejected

- assuming global postcomposition cancellation: not done;
- using S2130/S2185/S2269: not used;
- terminal/point/metadata substitution: not used;
- declaring the construction target as an axiom: not done.

## Reports read

`coord/reports/S2377-stack-presentation.md`,
`coord/reports/S2374-stack-cancellation.md`, and S2089/S2090 definitions.
