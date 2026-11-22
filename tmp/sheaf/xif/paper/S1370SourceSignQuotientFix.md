# S1370: consistent signature typing for the D5-D9 sign-quotient records

Date: 2026-10-30.  Status: Lean EXIT=0, no sorry, axioms
propext / Classical.choice / Quot.sound.

## Defect (S1360)

S1360 showed that the three records

* `SourceSignQuotientGeometricCore` (SourceSignQuotientConstruction.lean),
* `SourceCompletionSignQuotient` (SourceCompletion.lean),
* `SourceSignQuotientData` (SourceDefinition31Quantifiers.lean)

are logically inconsistent:

1. `xF_geometry : SourceOncePuncturedGeometry A.curve xF` gives
   `xF.signature = sourceTypeOneOne = oncePuncturedElliptic`;
2. `xKType` gives `xK.signature = sourceTypeOneLTorsion l`;
3. `xK_eq_extension : xK = xKExtension.result` and the old
   `SourceOrbicurveScalarExtension.signature_preserved` give
   `xK.signature = xF.signature`;
4. `oncePuncturedElliptic` has one puncture and `sourceTypeOneLTorsion l`
   has none, so the two signatures are different.

The three former Lean theorems were
`s1360SourceSignQuotientGeometricCore_false`,
`s1360SourceCompletionSignQuotient_false`,
`s1360SourceSignQuotientData_false`.

## Paper semantics (IUT I, Definition 3.1)

* (b), corpus lines 3131-3157: X_F is a once-punctured elliptic curve,
  i.e. type (1,1), and C_F is its stack-theoretic quotient by -1.
* (d), corpus lines 3185-3215: C_K is of type (1,l-tors)^`+-` over K,
  with K-core C_K = C_F x_F K, and determines X_K of type (1,l-tors).
  The K-core is the coarse base change; extracting l-th roots of the
  theta function ([EtTh], Definition 2.1) adds the l-torsion stacky
  decoration on the K-side.

Consequently the paper-faithful typing keeps X_F/C_F at (1,1) and
X_K/C_K at (1,l-tors)/(1,l-tors)^`+-`.  Retyping X_F/C_F as (1,l-tors)
(the other option in the task) would contradict Definition 3.1(b) and was
not used.

## Fix (minimal, source-level)

In `LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean`:

```
structure SourceOrbicurveScalarExtension ...
  result : Iut.HyperbolicOrbicurve K
  stackExtension : SourceEtaleStackScalarExtension F K X.stack
  target_stack : result.stack = stackExtension.result
  genus_preserved : result.signature.genus = X.signature.genus
```

Removed fields/lemmas:

* field `stackyOrders_preserved`;
* field `punctures_preserved`;
* theorem `signature_preserved : result.signature = X.signature`.

Added/kept:

* `genus_preserved` (kept, now the only preserved signature invariant);
* `signature_genus_preserved` (new wrapper theorem).

The structure still carries the actual base-changed stack
(`stackExtension`, `target_stack`); no object field was dropped or
replaced by a terminal/empty/fake carrier.  The scalar extension is now
the K-core extension: it preserves the coarse genus, while the K-side
l-tors decoration changes stacky orders and punctures.

Derived signature lemmas in `SourceSignQuotientData`:

* `xK_signature` now states `xK.signature = sourceTypeOneLTorsion l`;
* `cK_signature` now states `cK.signature = sourceTypeOneLTorsionPlusMinus l`;
* new `xK_genus`, `cK_genus`, `cF_genus` record the genus relations.

S1360 was updated accordingly: the three `_false` theorems were removed
and replaced by `s1360SignatureTyping_of_fields` plus
`s1360SourceSignQuotientGeometricCore_signature_typing`,
`s1360SourceCompletionSignQuotient_signature_typing`,
`s1360SourceSignQuotientData_signature_typing`.  Each proves the
record's signature data is exactly: X_F (1,1), X_K (1,l-tors), common
genus, distinct signatures.

## S1370 Lean contents

`tmp/sheaf/xif/paper/S1370SourceSignQuotientFix.lean` proves, without
False/explosion:

* `s1370_sourceTypeOneLTorsion_ne_sourceTypeOneOne`;
* `s1370_signature_typing`: under the fixed fields, X_F is (1,1),
  X_K is (1,l-tors), `xK.signature.genus = xF.signature.genus`, and
  `xK.signature != xF.signature` (the opposite of the old bridge);
* the same conjunction for all three records
  (`s1370SourceSignQuotientGeometricCore_signature_typing`,
  `...CompletionSignQuotient...`, `...SignQuotientData...`);
* C-side typing `cK = (1,l-tors)^+-`, `cK.genus = cF.genus`,
  `cF.genus = 1` for all three records;
* a signature-level shadow structure `S1370SignatureTyping`, inhabited
  by the four paper types `s1370PaperSignatureTyping`
  (so the signature constraints are satisfiable), with maps from each
  actual record into the shadow.

No `False`, `False.elim`, `absurd`, or `sorry` occurs in the proof.

## Verification

* S1370 source SHA256:
  `31A2982568C895A882FDEE20E34376CC0D31933DFA91C73BBABA1D5D156C1C18`
  (322 lines, 13246 bytes).
* Lean compile (lake env lean -j1 -R D:\lean -o ...):
  **EXIT=0**, log tmp/sheaf/xif/paper/S1370Compile.log, no warnings.
* All `#print axioms` outputs of S1370: only
  `propext`, `Classical.choice`, `Quot.sound`.
* Changed source file S1370 depends on:
  SourceDefinition31Quantifiers.lean, SHA256
  `0E6BBBF2536A5DB72DE5A17AAF0B0E9FF5432D4465928BBD54C7C7E7AD10AA81`
  (1823 lines).
  Rebuilt to olean with EXIT=0; SourceCompletion and
  SourceSignQuotientConstruction were also rebuilt with EXIT=0 (sources
  unchanged).
* Updated S1360 source SHA256:
  `17CA2C9A70F6CC3C9E4F8311425EB1E3FE7922F92885F2C609B81BC70F355157`
  (397 lines), EXIT=0.
* S1360 old compile log tmp/sheaf/xif/paper/S1360Compile.log is stale
  (it records the removed `_false` theorems); the current compile
  is tmp/sheaf/xif/paper/S1370S1360.log.

## Not done / boundaries

* No inhabitant of `SourceSignQuotientGeometricCore`,
  `SourceCompletionSignQuotient` or `SourceSignQuotientData` is
  constructed; the fix is a typing fix, not a construction of the source
  orbicurves.
* The l-torsion stacky enrichment of the K-side orbicurve is not
  constructed; it remains represented by the K-side object's certified
  (1,l-tors) geometry, as before.
* S1360's KCore records (`S1360KCoreBaseChange`,
  `S1360KCoreIdentification`) are unchanged apart from documentation and
  are consistent with the genus-only extension.
