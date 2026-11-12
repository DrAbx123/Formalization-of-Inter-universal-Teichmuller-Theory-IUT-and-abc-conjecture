# S2171: SourceCompletion / SourceSignQuotient first missing

Date: 2026-11-02. Layer: **O** (original Theta-link native source).
No target change, no fake, independent of 3.11/Eta.

## Files read

- `tmp/sheaf/xif/paper/S2162NativeSourceActual.lean`
- `LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean`
  (`SourceSignQuotientData`, `SourceNativeInitialThetaData`)
- `LeanFormal/IUT/IUTI/InitialTheta/SourceCompletion.lean`
  (`SourceCompletion`, `SourceCompletionSignQuotient`,
  `ofSourceSignQuotientData`)
- `LeanFormal/IUT/IUTI/HodgeTheater/SourceDefinition31NativeContractBridgeReduction.lean`
  (`ContractRootSignQuotientSupply`, `contractCanonicalFbar`)
- reports `S2153-native-totalization.md`, `S2162-native-source.md`

## Source object / domain / direction

- Source object: `S2162SourceCompletionRequired I`, equivalently the native
  source `S2153NativeSourceRequired I`.
- Domain: original O-layer arithmetic root; no S2040FirstMissing assumption.
- Direction: isolate the first block `SourceSignQuotientData` and give the
  exact component list of a pointwise `SourceCompletion` above
  `I.initial.arithmetic`.

## Deliverable

`tmp/sheaf/xif/paper/S2171SourceCompletionActual.lean`

```text
EXIT=0
olean=YES
lines=72
SHA256=D6F48F118C9E6B309FBAD8EDC3C2DCB86B949E95DA212CF75C91F1F2D87B2B06
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2171SourceCompletionActual.olean
axioms: propext, Classical.choice, Quot.sound
```

## BUILT

1. `S2171SourceSignQuotientRequired I :=
   Nonempty (SourceSignQuotientData I.initial.arithmetic)`.
2. `S2171ContractRootSignQuotientRequired l := ContractRootSignQuotientSupply.{0} l`,
   with `s2171ContractRootSignQuotient_iff` restating the tree definition.
3. `s2171SourceCompletion_requires_signQuotient`:
   any `SourceCompletion` above the paper root gives a source sign quotient.
4. `s2171NativeSource_requires_signQuotient`:
   any native source above the paper root gives a source sign quotient
   (`T.tuple.source` cast along `T.arithmetic = I.initial.arithmetic`).
5. `S2171SourceCompletionRequired I := S2162SourceCompletionRequiredProp I`,
   with definitional iff.

No inhabitant of the sign quotient, completion, or source is asserted.

## Exact first missing

```text
exists C : SourceCompletion.{0} l,
  C.arithmetic = I.initial.arithmetic
```

Its component list (all required):

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

Important: **fbar is not the first missing**. The tree already has
`contractCanonicalFbar S : SourceFbarExtension S.arithmetic`
(from `SourceDefinition31NativeContractBridgeReduction`), so the fbar slot
can be filled from the paper arithmetic root.

The first genuine block is `SourceSignQuotientData I.initial.arithmetic`.
Its first fields are the foundation orbicurve and quotient data:

```text
xF : Iut.HyperbolicOrbicurve I.initial.arithmetic.F
xF_geometry : SourceOncePuncturedGeometry A.curve xF
ellipticInvolution : xF.Hom xF
ellipticInvolution_squared
unique_elliptic_involution
signAction : Iut.OrbicurveSignAction xF
signAction_inversion_eq_ellipticInvolution
cF : Iut.HyperbolicOrbicurve A.F
quotient : Iut.OrbicurveSignInvariantMorphism signAction cF
quotientWitness : Iut.OrbicurveSignQuotientWitness signAction quotient
xFGroups / cFGroups : SourceOrbicurveGroupData ...
fGroupInclusion
xK / cK / xKExtension / cKExtension / xKType / cKType /
xK_eq_extension / cK_eq_extension
V / V_mod_bad / V_mod_bad_odd_residue_characteristic /
V_mod_bad_nonempty / V_section / V_eq_section /
V_mod_bijection / V_place_comap
epsilon : Iut.OrbicurveBoundaryCusp cK
```

The contract `SourceDefinition31Data` supplies arithmetic, selected/bad places,
reduction, torsion, orbicurve, section and cusp clauses, but **not** this
foundation orbicurve `xF` or the sign-quotient/universal-property data. The
tree's own audit records `ContractRootSignQuotientSupply` as the necessary
block:

```text
ContractRootSignQuotientSupply l :=
  ∀ S : SourceDefinition31Data, Nonempty (SourceSignQuotientData S.arithmetic)
```

No inhabitant of it is present.

## Why the completion is not constructed

- `SourceSignQuotientData` is not derivable from the contract fields; its
  first field is the actual foundation orbicurve, absent from
  `SourceDefinition31Data` (which only has abstract clause carriers).
- `SourceCompletion` additionally requires the sign quotient, arithmetic
  prelude/place-section, and clauses A-F; no constructor from a bare
  `SourceDefinition31Data` exists.
- `ContractNativeRecordBridge` / `PointwiseNativeTotalizationOverContractRoots`
  are the only tree-level sources of native T, and both are uninhabited.
- `SourceCompletion.ofSourceNative` goes native -> completion, not contract ->
  completion.

No xF, sign action, quotient witness, clause, or completion was fabricated.

## Consumer

`s2171SourceCompletion_requires_signQuotient` is the necessary projection.
A future `SourceSignQuotientData I.initial.arithmetic` plus fbar/prelude/clauses
assembles `SourceCompletion`, then S2162
`s2162NativeSourceOfCompletion` gives the native source; S2153 then needs
`NativeLattice` and S2148 the O(-D) line bundle.

## Next executable subgoal

```text
construct SourceSignQuotientData I.initial.arithmetic
```

starting with:

```text
xF : Iut.HyperbolicOrbicurve I.initial.arithmetic.F
xF_geometry : SourceOncePuncturedGeometry I.initial.arithmetic.curve xF
```

then the elliptic involution, sign action, quotient witness, groups/extension,
V/section data, and epsilon.

## Reports read

`coord/reports/S2153-native-totalization.md`,
`coord/reports/S2162-native-source.md`, and the bridge definitions in
`SourceDefinition31NativeContractBridgeReduction.lean`.
