# S1374: corrected signature typing for the D5-D9 sign-quotient records

Date: 2026-10-30.  Task: remove the S1360 `s1360*_false` contradiction by
fixing the signature typing of `SourceSignQuotientGeometricCore`,
`SourceCompletionSignQuotient` and `SourceSignQuotientData`, following
IUT I, Definition 3.1(b)/(d), without using `False` or explosion.

## Paper semantics

* Definition 3.1(b): the F-side curve `X_F` is once-punctured, type
  `(1,1)`; the quotient `C_F = X_F/(+-1)` is the `(1,1)^\pm` object.
* Definition 3.1(d): the K-side objects are `X_K` of type
  `(1,l-tors)` and `C_K` of type `(1,l-tors)^\pm`, with K-core
  `C_K = C_F x_F K`.
* The K-core base change is coarse: extracting l-th roots of the theta
  function ([EtTh], Definition 2.1) adds the l-torsion stacky decoration
  on the K-side.  It preserves the coarse genus, not the full signature
  (genus + stacky orders + punctures).

The fix therefore keeps the paper's F-side `(1,1)` typing and weakens
the scalar-extension record to genus preservation.  Retyping `X_F`/`C_F`
as `(1,l-tors)` was rejected because Definition 3.1(b) makes `X_F`
once-punctured.

## Source change

`LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean`:

* `SourceOrbicurveScalarExtension` no longer stores
  `stackyOrders_preserved` or `punctures_preserved`; it stores only
  `result`, `stackExtension`, `target_stack`, `genus_preserved`.
* the old `signature_preserved` theorem is removed;
  `SourceOrbicurveScalarExtension.signature_genus_preserved` records the
  only invariant preserved by the coarse base change.
* `SourceSignQuotientData.xK_signature` / `cK_signature` now state the
  paper types `sourceTypeOneLTorsion l` / `sourceTypeOneLTorsionPlusMinus l`;
  `xK_genus`, `cK_genus` and `cF_genus` are the genus consequences.

`tmp/sheaf/xif/paper/S1360D9OrbicurveSlotActual.lean` was rewritten to
use the fixed typing and no longer declares
`s1360SourceSignQuotientGeometricCore_false`,
`s1360SourceCompletionSignQuotient_false` or
`s1360SourceSignQuotientData_false`.  Its audit probe checks the new
signature-typing declarations.

## S1374 contents

`tmp/sheaf/xif/paper/S1374SourceSignQuotientFix.lean` proves, from the
fixed records and `SourceOrbicurveScalarExtension.genus_preserved` only:

* `s1374_signature_typing`: `xF.signature = (1,1)`,
  `xK.signature = (1,l-tors)`, common genus, and
  `xK.signature != xF.signature`.
* `s1374_cK_typing`: `cK.signature = (1,l-tors)^\pm`, common genus,
  and `cF.signature.genus = 1`.
* `s1374SourceSignQuotientGeometricCore_signature_typing`,
  `s1374SourceCompletionSignQuotient_signature_typing` and
  `s1374SourceSignQuotientData_signature_typing`, plus the C-side
  versions, apply the generic results to the three records.
* `s1374_no_full_signature_preservation`: under `(1,1)` on the
  F-side and `(1,l-tors)` on the extension result, full signature
  equality is impossible.  This is the corrected form of the old bridge;
  it is a negation, not a `False`/explosion step.
* `S1374SignatureTyping` and `s1374PaperSignatureTyping`: the
  signature-level constraints are inhabited by the paper's four types
  `(1,1)`, `(1,l-tors)`, `(1,1)^\pm`, `(1,l-tors)^\pm`.

No geometric record is constructed, and no terminal/empty carrier is
used.  `S1360D9OrbicurveSlot` and `S1360OrbicurveSlotAtK` still have no
asserted inhabitant.

## Verification

* Compile: `lake env lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1374SourceSignQuotientFix.olean tmp/sheaf/xif/paper/S1374SourceSignQuotientFix.lean`
* EXIT=0; log `S1374Compile.log`; no warnings.
* SHA256: `9BAC620C58F9A5F8AD4D11C6FECF193CCA21C008B75529B44945671242C725D4`
* 359 lines, 14462 bytes.
* Axioms: only `propext`, `Classical.choice`, `Quot.sound`.
* No `sorry`, `admit`, `axiom`, `native_decide`, or `False` in the file.

Related: the primary fix record is `S1370SourceSignQuotientFix.lean`
(SHA256 `31A2982568C895A882FDEE20E34376CC0D31933DFA91C73BBABA1D5D156C1C18`,
EXIT=0).  S1374 is an independent verification of the same corrected
typing.  Current S1360 SHA256 is
`17CA2C9A70F6CC3C9E4F8311425EB1E3FE7922F92885F2C609B81BC70F355157`.
