# S2177: xF / xF_geometry reduced to nondegenerate D6 orbicurve realization

Date: 2026-11-02. Layer: **O** (original Theta-link source orbicurve).
No target change, no fake, independent of 3.11/Eta.

## Files read

- `tmp/sheaf/xif/paper/S2171SourceCompletionActual.lean`
- `Iut/Foundations/Orbicurve.lean` (`EtaleStackOverField`,
  `OrbicurveGeometry`, `HyperbolicOrbicurve`)
- `LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean`
  (`SourceSignQuotientData`, `SourceOncePuncturedGeometry`,
  `sourceTypeOneOne`)
- `LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31OrbicurveInstance.lean`
  (terminal stack, no geometry)
- `LeanFormal/IUT/IUTII/Frobenioid/Example36OrbicurveFeasibility.lean`
  (`MissingD6GeometricRealization`, degenerate point-fiber orbicurve)
- reports `S2162-native-source.md`, `S2171-source-completion.md`

## Source object / domain / direction

- Source object: first two fields of `SourceSignQuotientData` at
  `I.initial.arithmetic`:
  `xF : Iut.HyperbolicOrbicurve A.F` and
  `xF_geometry : SourceOncePuncturedGeometry A.curve xF`.
- Domain: original O-layer, no SourceCompletion/FirstMissing assumption.
- Direction: reduce xF/xF_geometry to an actual nondegenerate geometric stack
  realization; reject the degenerate point-fiber signature insertion.

## Deliverable

`tmp/sheaf/xif/paper/S2177SignQuotientDataActual.lean`

```text
EXIT=0
olean=YES
lines=85
SHA256=23538F56256941BFE1B21991EAD781D826F3597E744D00B347FE269D52C3CB4C
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2177SignQuotientDataActual.olean
axioms: propext, Classical.choice, Quot.sound
```

## BUILT

1. `S2177ActualD6Orbicurve A`:
   - `D : MissingD6GeometricRealization A.F` (actual curve + etale stack fiber
     + effective descent + nondegenerate + curve-point realization),
   - `curve_eq : D.curve = A.curve`.
2. `s2177_exists_hyperbolicOrbicurve`:
   from D, `∃ xF : HyperbolicOrbicurve A.F, xF.signature = sourceTypeOneOne`.
3. `s2177_exists_xF_geometry`:
   from D, `∃ xF, Nonempty (SourceOncePuncturedGeometry D.D.curve xF)`.
4. `s2177_exists_xF_geometry_for_arithmetic`:
   transport along `D.curve_eq` to
   `Nonempty (SourceOncePuncturedGeometry A.curve xF)`.
5. `S2177ActualD6OrbicurveRequired A := Nonempty (S2177ActualD6Orbicurve A)`,
   with definitional iff.

The xF and xF_geometry are **constructed conditionally** from actual D6 data,
not by inserting a signature into a point fiber.

## PROVED / actual

- `MissingD6GeometricRealization.exists_oncePuncturedHyperbolicOrbicurve`
  supplies the actual `HyperbolicOrbicurve` with
  `oncePuncturedElliptic` signature.
- `oncePuncturedElliptic = sourceTypeOneOne` is definitional (same genus 1,
  empty stacky orders, one puncture), so `SourceOncePuncturedGeometry` is
  filled by its only field `signature`.
- The curve equality field allows transport from D's curve to
  `A.curve`.

## Exact first missing

```text
S2177ActualD6Orbicurve A
  = (D : MissingD6GeometricRealization A.F)
    × (D.curve = A.curve)
```

i.e. exactly:

```text
curve : PuncturedEllipticCurve A.F
fiber : Iut.EtaleStackPseudofunctor A.F
isStack : fiber.IsStack (SchemeOverField.etaleTopology A.F)
nondegenerate : ¬ IsPointFiber fiber
curvePointRealization :
  ∃ f : fiber.obj (baseSchemeObject A.F) → curve.curve.toProjective.Point,
    Function.Surjective f
curve_eq : curve = A.curve
```

No inhabitant is asserted. The tree's
`Example36OrbicurveFeasibility.MissingD6GeometricRealization` records this exact
D6 gap; `SourceDefinition31OrbicurveInstance` proves the terminal constant
stack has `orbicurveSignature = none` and no `OrbicurveGeometry`, so it
cannot be the carrier.

## Rejected fake route

`degeneratePointFiberOrbicurve F` is a HyperbolicOrbicurve with the correct
`oncePuncturedElliptic` signature, but its fiber is the one-point constant
fiber and the source file says explicitly it is **not** the source orbicurve.
Its `missingD6` nondegeneracy condition fails. Inserting
`orbicurveSignature := some sourceTypeOneOne` into an arbitrary constant
fiber would be a metadata certificate without geometric realization; this file
does not do that.

## Consumer

An inhabitant of `S2177ActualD6Orbicurve A` supplies xF and xF_geometry, hence
the first two fields of `SourceSignQuotientData A`; then the remaining sign
action/quotient/groups/extension/V/epsilon fields, clauses A-F, and the native
source/completion chain can proceed. No 3.11/Eta assumption.

## Next executable subgoal

```text
construct MissingD6GeometricRealization A.F
  with curve = A.curve
```

i.e. an actual nondegenerate etale-stack fiber with effective descent and a
surjective realization of the curve's projective points at the base scheme.
No such stack is constructed in the tree/Mathlib.

## Reports read

`coord/reports/S2162-native-source.md`,
`coord/reports/S2171-source-completion.md`, plus the D6 feasibility and
terminal-stack audits above.
