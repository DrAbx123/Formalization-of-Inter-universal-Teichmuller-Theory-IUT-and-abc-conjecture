# S1360: D9 orbicurve slot — actual coarse quotient / exact X at K

Date: 2026-10-30. S1360 file was absent; created exact target + actual S1319
coarse-quotient result. No terminal object.

## Current evidence (supersedes all pre-fix text below)

Current S1360 file: `S1360D9OrbicurveSlotActual.lean`, SHA256
`17CA2C9A70F6CC3C9E4F8311425EB1E3FE7922F92885F2C609B81BC70F355157`,
397 lines / 17051 bytes, `lake env lean` EXIT=0.  The three former
`s1360*_false` theorems are absent from it.

Current independent S1374 verification: `S1374SourceSignQuotientFix.lean`,
SHA256 `9BAC620C58F9A5F8AD4D11C6FECF193CCA21C008B75529B44945671242C725D4`,
359 lines / 14462 bytes, EXIT=0, axioms `propext` / `Classical.choice` /
`Quot.sound`.  Fresh recheck 2026-10-30 22:48: `lake env lean` on both
files returned EXIT=0 with no warnings or `sorryAx`.

STALE (do not quote as current): the old S1360 SHA
`7B6BB175E731574E3BA7CF108EFBEF5E4544B08576906AF3E075D62B058A2A5E`,
any earlier S1374 hash beginning `33B9...`, the three `_false`
declarations, and the pre-fix logs `S1360Build.pre-fix.log` /
`S1360Compile.pre-fix.log`.  Current logs are
`S1360CompileFixed.log`, `S1370Compile.log`, `S1374Compile.log`.

## Actual (S1319, reused)

S1319SourceOrbicurveClause l is the actual D6 boundary clause from the
concrete Gaussian curve:
* actual coarse quotient X_K/(+-1) at the point/quotient level;
* actual punctured points, sign involution, quotient map;
* quotient map surjective and nondegenerate (two-point fibre);
* actual l-torsion exact sequence as the clause exactSequence slot;
* actual nonterminal point-level quotient, not the identity/terminal cover.

S1360 file proves:
  s1360S1319Coarse_actual :
    (S1319SourceOrbicurveClause l).curve = S1319Curve l

## Exact target

  S1360OrbicurveFirstField l := Iut.HyperbolicOrbicurve (S1280Arithmetic l).K

  structure S1360OrbicurveSlotAtK (l) where
    X : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K
    nonterminal : S1319NonterminalFiber X
    signature : X.signature = Iut.OrbicurveSignature.oncePuncturedElliptic
    groups : Iut.OrbicurveFundamentalGroupData X
      (Iut.AbsoluteGaloisProfinite (S1280Arithmetic l).K)

No inhabitant is asserted.  This is the exact D9 orbicurve slot object: an
actual nonterminal stack/fiber HyperbolicOrbicurve over K with certified
once-punctured elliptic signature and actual orbifold Pi data.

## Exact first field

X : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K

After X:
* nonterminal stack/fiber certificate (S1319NonterminalFiber X);
* signature certificate;
* orbifold fundamental-group data.
For the K-core identification, the sign-quotient cK carrier must be identified
with this X/K carrier; that identification is the next exact field and is not
constructed here.

S1319 has the point-level coarse quotient and nonterminal cover, but does not
construct the actual etale stack/fiber object HyperbolicOrbicurve K.  The
Example36 helper realizedHyperbolicOrbicurve needs a MissingD6GeometricRealization
fiber; the available degenerate point-fiber orbicurve is explicitly negative
and is not used.

## Status

Lean EXIT=0.  No terminal/degenerate object used; no weak Prop/Nonempty gate
for X.

## 2026-10-30 22:15 update — STALE pre-fix record (do not quote as current; superseded below)

Pre-fix file (STALE): S1360D9OrbicurveSlotActual.lean, SHA256
7B6BB175E731574E3BA7CF108EFBEF5E4544B08576906AF3E075D62B058A2A5E,
372 lines, 16478 bytes.  Its pre-fix logs `S1360Build.pre-fix.log` and
`S1360Compile.pre-fix.log` are STALE.  Compile:
lake env lean -o ...olean -i ...ilean
tmp/sheaf/xif/paper/S1360D9OrbicurveSlotActual.lean, EXIT=0.  All audited
declarations depend only on propext, Classical.choice, Quot.sound.

Contents:

* S1360OrbicurveSlotAtK maps exactly to S1319OrbifoldPiData; an inhabitant
  would fill the S1319 orbifold-Pi gap.
* S1360PaperOrbicurveSlotAtK / S1360D9OrbicurveSlot: the paper-faithful
  D9 slot, with X.signature = sourceTypeOneLTorsion l.
* Signature correction: oncePuncturedElliptic (S1319, type (1,1)) is not
  sourceTypeOneLTorsion l (paper D9, type (1,l-tors));
  s1360OncePunctured_ne_sourceTypeOneLTorsion proves it, and
  S1360OrbicurveSlotAtK.signature_ne_paper proves the S1319
  once-punctured slot cannot be the paper D9 slot.
* S1360OrbicurvePrefixAtK / S1360OrbicurvePrefixOfMissingD6: from
  Example36's exact open input MissingD6GeometricRealization, the actual
  prefix (X, nonterminal, once-punctured signature) is constructed; hence
  a supplied D6 realization inhabits the exact first field
  (s1360FirstField_of_missingD6).  The D6 realization itself is not
  constructed.
* S1360KCoreBaseChange / S1360KCoreIdentification: the paper-faithful
  K-core record — C_K is the scalar extension of an actual F-side C_F,
  C_K has signature (1,l-tors)^+-, and X carries the finite-etale cover
  X -> C_K.  The earlier X = extension-of-once-punctured-X_F version was
  removed because it is inconsistent (next item).
* Major consistency result (STALE pre-fix diagnosis; superseded by the
  22:35/22:40 updates at the end of this file): the then-existing source
  sign-quotient records were uninhabited.
  SourceSignQuotientGeometricCore.xF_geometry forces
  xF.signature = sourceTypeOneOne, xKType forces
  xK.signature = sourceTypeOneLTorsion l, and the then-existing
  SourceOrbicurveScalarExtension.signature_preserved plus
  xK_eq_extension forced those two signatures equal; but they differ
  (punctures 1 vs 0).  The former Lean theorems were
  s1360SourceSignQuotientGeometricCore_false,
  s1360SourceCompletionSignQuotient_false and
  s1360SourceSignQuotientData_false.  This was a defect in the then-current
  D5-D9 signature typing, not a construction of X; the paper-faithful
  K-core replacement is S1360KCoreBaseChange /
  S1360KCoreIdentification.  The three `_false` theorems existed only in
  the stale 7B6... file and are absent from the current 17CA... file.
* No-terminal/no-point-fiber controls: the terminal constant stack cannot
  be a hyperbolic-orbicurve carrier; a point fiber is not
  S1319NonterminalFiber; the Example36 degenerate point-fiber orbicurve
  fails nonterminality; and a point fiber has no surjective realization
  of the actual Gaussian curve points.

No inhabitant of S1360D9OrbicurveSlot or S1360OrbicurveSlotAtK is
asserted.  The exact first field remains
Iut.HyperbolicOrbicurve (S1280Arithmetic l).K.


## 2026-10-30 22:35 update: signature typing fixed (S1370)

The three `_false` theorems were removed.  The defect was in the shared
`SourceOrbicurveScalarExtension`: it asserted full signature preservation
(genus, stacky orders, punctures) and the records identified the
`(1,l-tors)` K-side objects with the extension result.  Per IUT I,
Definition 3.1(b)/(d), X_F stays `(1,1)` and C_F stays `(1,1)^\pm` on
the F-side, while X_K/C_K are `(1,l-tors)` / `(1,l-tors)^+-` on the
K-side; the K-core base change preserves only the genus.  `signature_preserved`,
`stackyOrders_preserved` and `punctures_preserved` were removed;
`genus_preserved` remains and `signature_genus_preserved` is added.

The records now force the F-side and K-side signatures to be distinct
(`s1360*_signature_typing`), so the old bridge and the three `False`
theorems are gone.  New file:
tmp/sheaf/xif/paper/S1370SourceSignQuotientFix.lean, SHA256
31A2982568C895A882FDEE20E34376CC0D31933DFA91C73BBABA1D5D156C1C18,
EXIT=0, axioms propext / Classical.choice / Quot.sound.  Current S1360
SHA256 is 17CA2C9A70F6CC3C9E4F8311425EB1E3FE7922F92885F2C609B81BC70F355157.

## 2026-10-30 22:40 independent S1374 verification

tmp/sheaf/xif/paper/S1374SourceSignQuotientFix.lean, SHA256
9BAC620C58F9A5F8AD4D11C6FECF193CCA21C008B75529B44945671242C725D4,
359 lines, EXIT=0, no warnings, axioms propext / Classical.choice /
Quot.sound.  It independently re-derives the fixed typing for all three
records and both X/C sides from `SourceOrbicurveScalarExtension.genus_preserved`
only: X_F (1,1), X_K (1,l-tors), common genus, X_K.signature != X_F.signature,
and C_K (1,l-tors)^+-, genus one.  No `False`, `sorry`, `axiom` or terminal
carrier is used.  The file is a verification/consistency certificate for the
source fix in SourceDefinition31Quantifiers, not a new geometric construction.

The earlier S1374 SHA beginning `33B9...` is STALE; the current SHA is
`9BAC...` above.  The pre-fix logs `S1360Build.pre-fix.log` and
`S1360Compile.pre-fix.log` remain only as archived STALE evidence; the
current logs are `S1360CompileFixed.log`, `S1370Compile.log` and
`S1374Compile.log`.  Documentation-only update; no Lean source was
touched; EXIT=0.
