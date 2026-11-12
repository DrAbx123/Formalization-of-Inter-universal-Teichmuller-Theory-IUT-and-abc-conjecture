# S2153: native totalization decomposition / NativeLattice first missing

Date: 2026-11-02. Layer: **O** (original Theta-link / q-pilot O(-D) donor).
No target change, no fake, independent of 3.11/Eta.

## Files read

- `tmp/sheaf/xif/paper/S2148PaperLineBundleActual.lean`
- `tmp/sheaf/n8/closure/NativeInput.lean`
- `LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean`
  (`SourceNativeInitialThetaData`)
- `LeanFormal/IUT/IUTI/HodgeTheater/SourceHodgeTheaterFamily.lean`
- `LeanFormal/IUT/IUTI/HodgeTheater/SourceDefinition31NativeContractBridgeReduction.lean`
  (`ContractNativeRecordBridge`, `PointwiseNativeTotalizationOverContractRoots`)
- `tmp/sheaf/xif/paper/OrigXiFPaperLineBundleActual.lean`

## Source object / domain / direction

- Source: `OrigXiFPaperLineBundleData I`, i.e. `X : N8NativeInput l` with
  `X.S.arithmetic = I.initial.arithmetic`.
- Domain: original O-layer native q-pilot arithmetic root; no normalized model,
  no S2040FirstMissing assumption.
- Direction: decompose the native totalization into the native source datum and
  the actual Hodge-theater lattice; isolate the exact first missing components.

## Deliverable

`tmp/sheaf/xif/paper/S2153NativeTotalizationActual.lean`

```text
EXIT=0
olean=YES
lines=110
SHA256=69ADB1686A72AEBA4BA2A8F609566CFB19B2E1F04189E3F22D7B8765C70A8979
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2153NativeTotalizationActual.olean
axioms: propext, Classical.choice, Quot.sound
```

## BUILT

1. `S2153NativeSourceRequired I`:
   `T : SourceNativeInitialThetaData l`,
   `T.arithmetic = I.initial.arithmetic`.
2. `S2153NativeLatticeRequired T := NativeLattice T`.
3. `S2153NativeComponentsRequired I`: native source above the paper arithmetic
   root plus its lattice.
4. `s2153NativeInputOfComponents`: components -> `N8NativeInput l`.
5. `s2153NativeTotalizationOfComponents`: components -> exact
   `OrigXiFPaperLineBundleData` shape.
6. `s2153NativeTotalizationRequired_iff_components`:
   `Nonempty NativeTotalization ↔ Nonempty Components` — actual equivalence.
7. `s2153NativeTotalizationRequired_components_explicit`:
   `↔ ∃ T : SourceNativeInitialThetaData l,
       T.arithmetic = I.initial.arithmetic ∧ Nonempty (NativeLattice T)`.

All are actual definitions/theorems, not inhabitants of the missing data.

## PROVED / actual

- construction from components to `N8NativeInput`;
- arithmetic-root equality is preserved;
- exact decomposition equivalence is kernel-checked;
- no `Nonempty` of `OrigXiFPaperLineBundleData` is asserted.

## MISSING exact

```text
S2153NativeTotalizationRequired I
  = Nonempty (OrigXiFPaperLineBundleData I)
  ⇔ ∃ T : SourceNativeInitialThetaData l,
      T.arithmetic = I.initial.arithmetic
      ∧ Nonempty (NativeLattice T)
```

The first missing is therefore exactly:

1. a native totalization `T` of the paper arithmetic root
   (`T.arithmetic = I.initial.arithmetic`), and
2. an actual `NativeLattice T`.

## Required NativeLattice components

`NativeLattice T` consists of:

```text
family : SourceHodgeTheaterFamily l (NativePlaces T)
  index : Type
  theater : index → HodgeTheater l (NativePlaces T)
  distinct : Function.Injective theater
  link : ∀ i j, HodgeTheaterLink (theater i) (theater j)
  link_refl : ∀ i, link i i = HodgeTheaterLink.refl (theater i)
  link_symm : ∀ i j, HodgeTheaterLink.symm (link i j) = link j i
  link_trans : ∀ i j k,
    HodgeTheaterLink.trans (link i j) (link j k) = link i k
  permutation : Equiv.Perm index
  permutationLink : ∀ i, HodgeTheaterLink (theater (permutation i)) (theater i)
  permutation_naturality : ∀ i j,
    HodgeTheaterLink.trans (link (permutation i) (permutation j))
      (permutationLink j) =
    HodgeTheaterLink.trans (permutationLink i) (link i j)
arithmetic_alignment : ∀ i, (family.theater i).arithmetic = T.arithmetic
```

No component is produced in the tree for an arbitrary paper `I`; the native
source itself is also missing.

## Why this is not constructed

- `I.initial : SourceDefinition31Data` supplies the arithmetic root and the
  source clauses, but not `SourceNativeInitialThetaData` (which carries
  `InitialThetaArithmeticData` + `SourceInitialThetaTuple` + clauses A-F).
- `N8NativeInput` additionally requires a full `NativeLattice`: a family of
  actual Hodge theaters with links, permutation coherence, and arithmetic
  alignment.
- The tree's `ContractNativeRecordBridge` / `PointwiseNativeTotalizationOverContractRoots`
  are recorded as exact bridges; neither has an inhabitant on this path.
- `SourceCompletion.toSourceNativeInitialThetaData` needs a `SourceCompletion`,
  not a bare `SourceDefinition31Data`.

No `arithmetic_root_eq` or lattice was fabricated.

## Consumer

Once `S2153NativeComponentsRequired I` is inhabited,
`s2153NativeTotalizationOfComponents` yields
`OrigXiFPaperLineBundleData I`, hence the actual O(-D) carrier
`OrigXiFPaperLineBundleCarrier I D` and the line-bundle slot of the paper O
interface. The strip/q skeleton from S2148 is separate.

## Next executable subgoal

```text
S2153NativeSourceRequired I:
  T : SourceNativeInitialThetaData l,
  T.arithmetic = I.initial.arithmetic
```

then

```text
Nonempty (NativeLattice T):
  family of actual Hodge theaters over NativePlaces T
  + links/permutation coherence
  + arithmetic_alignment
```

This is independent of 3.11/Eta.

## Reports read

`coord/reports/S2148-paper-line-bundle.md`; the native-bridge definitions in
`SourceDefinition31NativeContractBridgeReduction.lean` and
`tmp/sheaf/n8/closure/NativeInput.lean`.
