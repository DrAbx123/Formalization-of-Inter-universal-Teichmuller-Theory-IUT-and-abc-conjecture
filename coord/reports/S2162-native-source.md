# S2162: pointwise native source / SourceCompletion reduction

Date: 2026-11-02. Layer: **O** (original Theta-link native q-pilot source).
No target change, no fake, independent of 3.11/Eta.

## Files read

- `tmp/sheaf/xif/paper/S2153NativeTotalizationActual.lean`
- `LeanFormal/IUT/IUTI/InitialTheta/SourceCompletion.lean`
- `LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean`
- `LeanFormal/IUT/IUTI/HodgeTheater/SourceDefinition31NativeContractBridgeReduction.lean`
- `tmp/sheaf/n8/closure/NativeInput.lean`
- reports `S2148-paper-line-bundle.md`, `S2153-native-totalization.md`

## Source object / domain / direction

- Source object: `S2153NativeSourceRequired I`, i.e.
  `T : SourceNativeInitialThetaData l` with
  `T.arithmetic = I.initial.arithmetic`.
- Domain: original O-layer arithmetic root; no S2040FirstMissing assumption.
- Direction: reduce pointwise native source to `SourceCompletion` above the
  paper root; expose the exact clauses and the tree's contract bridge route.

## Deliverable

`tmp/sheaf/xif/paper/S2162NativeSourceActual.lean`

```text
EXIT=0
olean=YES
lines=100
SHA256=B8D0D6655050ED97612A8E3034A7FA870854249CEB12DEDF228AFC1C44665874
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2162NativeSourceActual.olean
axioms: propext, Classical.choice, Quot.sound
```

## BUILT

1. `S2162SourceCompletionRequired I`:
   `C : SourceCompletion.{0} l`,
   `C.arithmetic = I.initial.arithmetic`.
2. `s2162NativeSourceOfCompletion`: completion above root -> native source
   `T = C.toSourceNativeInitialThetaData`.
3. `s2162CompletionOfNativeSource`: native source -> completion
   `SourceCompletion.ofSourceNative T`.
4. `s2162NativeSourceRequired_iff_completion`:
   `Nonempty (S2153NativeSourceRequired I) ↔
    Nonempty (S2162SourceCompletionRequired I)` — actual equivalence.
5. `s2162NativeSource_of_contractBridge`:
   `ContractNativeRecordBridge.{0} l -> Nonempty (S2153NativeSourceRequired I)`.
6. `s2162NativeSource_of_pointwiseTotalization`:
   `PointwiseNativeTotalizationOverContractRoots.{0} l ->
    Nonempty (S2153NativeSourceRequired I)`.
7. `S2162SourceCompletionRequiredProp I := Nonempty ...`, with definitional iff.

No inhabitant of 1/5/6 is asserted.

## Exact first missing

```text
Nonempty (S2162SourceCompletionRequired I)
= exists C : SourceCompletion.{0} l,
    C.arithmetic = I.initial.arithmetic
```

`SourceCompletion` components (all required):

```text
arithmetic : InitialThetaArithmeticData.{0} l
fbar : SourceFbarExtension arithmetic
signQuotient : SourceCompletionSignQuotient arithmetic
arithmeticPrelude : SourceArithmeticPrelude arithmetic
arithmeticPrelude_placeSection :
  arithmeticPrelude.placeSection = signQuotient.V_section
clauseA : SourceClauseA arithmetic signQuotient.toSourceSignQuotientData
clauseB : SourceClauseB ... clauseA
clauseC : SourceClauseC ... clauseA clauseB
clauseD : SourceClauseD ... clauseA clauseB clauseC
clauseE : SourceClauseE ... clauseA clauseB clauseC clauseD
clauseF : SourceClauseF ... clauseA clauseB clauseC clauseD clauseE
```

`SourceNativeInitialThetaData` is exactly
`arithmetic + tuple (fbar/source) + clauses A-F`; `SourceCompletion` is the
same data with the `SourceCompletionSignQuotient` presentation.

## Bridge components (no inhabitant)

- `ContractNativeRecordBridge.{0} l`:
  `∃ Ψ : SourceNativeInitialThetaData -> SourceDefinition31Data,
    ∀ T, (Ψ T).arithmetic = T.arithmetic`.
  This is stronger than the pointwise source requirement; it supplies the
  pointwise native T for every contract, including `I.initial`.
- `PointwiseNativeTotalizationOverContractRoots.{0} l`:
  `∀ S, ∃ T, T.arithmetic = S.arithmetic`; equivalent to the bridge by the
  tree theorem `contractNativeRecordBridge_iff_pointwiseTotalization`.
- Necessary block:
  `ContractRootSignQuotientSupply l :=
    ∀ S, Nonempty (SourceSignQuotientData S.arithmetic)`
  (tree theorem: a contract-native bridge implies this supply). It is not an
  inhabitant.

## Why not constructed

- `I.initial` supplies arithmetic and contract clauses, but no
  `SourceCompletion` and no `SourceSignQuotientData I.initial.arithmetic`;
- `SourceCompletion` also needs `fbar`, `SourceArithmeticPrelude` and clauses
  A-F; these are not derivable from the contract record alone;
- the tree records the bridge and sign-quotient supply as open bridges, with no
  inhabitant.

No tuple, clause, fbar or sign quotient was fabricated.

## Consumer

`s2162NativeSourceOfCompletion` or either bridge theorem yields
`S2153NativeSourceRequired I`, then (with the lattice missing) S2153's
`S2153NativeTotalizationRequired I`; eventually
`OrigXiFPaperLineBundleData I` and the actual O(-D) carrier. No S2040
FirstMissing assumption is used.

## Next executable subgoal

```text
construct C : SourceCompletion.{0} l with
  C.arithmetic = I.initial.arithmetic
```

or, equivalently for the paper route, construct
`PointwiseNativeTotalizationOverContractRoots l`; then supply
`Nonempty (NativeLattice T)` from S2153.

## Reports read

`coord/reports/S2148-paper-line-bundle.md`,
`coord/reports/S2153-native-totalization.md`, plus the bridge definitions in
`SourceDefinition31NativeContractBridgeReduction.lean`.
