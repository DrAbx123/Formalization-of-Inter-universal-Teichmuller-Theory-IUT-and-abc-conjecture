# S2148: paper line-bundle native totalization / S2038 O strip-q skeleton

Date: 2026-11-02. Layer: **O** (original Theta-link). No target change, no fake.

## Files read

- `tmp/sheaf/xif/paper/OrigXiFPaperLineBundleActual.lean`
- `tmp/sheaf/xif/paper/OrigXiFPaperLineBundleODActual.lean`
- `tmp/sheaf/xif/paper/S2040ActualThetaLink312.lean` (`S2038PaperOActual`,
  `S2040FirstMissing`)
- `tmp/sheaf/xif/paper/ThetaLinkLogKummerActual.lean`
- `tmp/sheaf/n8/closure/NativeInput.lean`
- `LeanFormal/IUT/IUTI/HodgeTheater/SourceDefinition31NativeContractBridgeReduction.lean`
- `coord/reports/S2040-actual-theta-link.md`, `S2040-four-qpilot-audit.md`

## Source object / domain / direction

- Source object: `OrigXiFPaperLineBundleData` / S2038 paper O interface.
- Domain: original-text O layer; paper `I.initial` arithmetic root and actual
  native q-pilot `O(-D)`.
- Direction: construct the first non-3.11/Eta subgoal — native arithmetic-root
  totalization — and isolate the strip/q skeleton of `S2038PaperOActual` with
  exact fields. No S2040FirstMissing assumption.

## Deliverable

`tmp/sheaf/xif/paper/S2148PaperLineBundleActual.lean`

```text
EXIT=0
olean=YES
lines=113
SHA256=0535EEB970E12C669B34BFF425938A1863C84FB5AFBE2C27512D64AAAEB25A9D
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2148PaperLineBundleActual.olean
axioms: propext, Classical.choice, Quot.sound
```

## BUILT

1. `S2148PaperOStripSkeleton`: exact q/strip fields
   - `q`, `q_eq_source : q = I.oneColumnQAtZero`,
   - `q_pos : 0 < q`, `q_lt_one : q < 1`,
   - `qPilotStrip = I.primeStripAt 1 0`,
   - `thetaPilotStrip = I.primeStripAt 0 0`.
2. `s2148PaperOStripSkeleton (hq : I.oneColumnQAtZero < 1)`: actual skeleton;
   positivity and both strip equalities are proved, only `q < 1` is an
   explicit hypothesis.
3. `S2148FourQPilotIdentifications O`: the exact four-field conjunction.
4. `S2148PaperOInterface O`: skeleton plus the four identifications, the
   local exact form of `S2038PaperOActual` q/strips/paperO_identifications.
5. `s2148PaperOInterfaceOfSkeleton`: skeleton + four identifications ->
   exact interface.
6. `S2148NativeArithmeticRootData I := OrigXiFPaperLineBundleData I`.
7. `S2148NativeArithmeticRootRequired I := Nonempty (OrigXiFPaperLineBundleData I)`,
   with `s2148NativeArithmeticRootRequired_iff : ... ↔ Nonempty ...`
   definitional.
8. `S2148NativeArithmeticRootObligation I`: field-explicit first missing
   `X : N8NativeInput l`, `X.S.arithmetic = I.initial.arithmetic`.
No inhabitant of 7/8 is asserted.

## PROVED / actual

- `I.oneColumnQAtZero_pos` from `ThetaLinkLogKummerActual`.
- `I.primeStripAt 1 0`, `I.primeStripAt 0 0` are actual source strips.
- The skeleton is kernel-checked; q<1 is not derived from bare input.

## MISSING exact

```text
S2148NativeArithmeticRootRequired I
  = Nonempty (OrigXiFPaperLineBundleData I)
  = exists X : N8NativeInput l, X.S.arithmetic = I.initial.arithmetic
```

This is the exact first field of the O(-D) line-bundle donor. It is not
constructible from `I : OriginalInput` alone:

- `I.initial : SourceDefinition31Data` has the arithmetic root but no native
  source/lattice package `X : N8NativeInput l`;
- `N8NativeInput` requires a `SourceNativeInitialThetaData` plus a
  `NativeLattice` (Hodge-theater family with arithmetic alignment);
- the tree records the bridge as `PointwiseNativeTotalizationOverContractRoots`
  / `ContractNativeRecordBridge`, both without an inhabitant on this path.

No `arithmetic_root_eq` witness was fabricated.

## Import/namespace caveat

`OrigXiFPaperLineBundleActual.lean` imports the old root
`tmp.sheaf.xif.PaperQPilotObject`; S2040ActualThetaLink312 imports
`tmp.sheaf.xif.paper.PaperQPilotObject`. The two modules declare the same
`PaperQPilotObject` names and cannot be co-imported. S2148 therefore lives on
the OrigXiF root and restates the four-field conjunction / paper O interface
locally; these are definitionally the same frozen fields, not a new target.
The native data alias is exactly `OrigXiFPaperLineBundleData`.

## Consumer

A future inhabitant of `S2148NativeArithmeticRootObligation` supplies
`OrigXiFPaperLineBundleData`, hence the actual O(-D) carrier
`OrigXiFPaperLineBundleCarrier I D`, and can fill the line-bundle component
of the S2040 paper O interface. The strip/q skeleton fills the strip/q part
modulo `q < 1`; the four paper identifications remain separate missing items
(3.11/Eta for log-Kummer/scalar; see S2040 audit).

## Next executable subgoal

```text
construct X : N8NativeInput l with X.S.arithmetic = I.initial.arithmetic
```

i.e. a pointwise native totalization of the paper arithmetic root together with
its actual lattice. This is independent of 3.11/Eta.

## Reports read

`coord/reports/S2040-actual-theta-link.md` (line-bundle native totalization
first field; O(-D) vs completion-trivial distinction);
`coord/reports/S2040-four-qpilot-audit.md` (four identifications and
3.11/Eta ordering).
