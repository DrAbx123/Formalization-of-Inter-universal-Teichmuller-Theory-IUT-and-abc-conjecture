# S2188: nondegenerate D6 stack realization / exact first missing

Date: 2026-11-02. Layer: **O** (source orbicurve D6). No target change,
no fake, independent of 3.11/Eta.

## Files read

- `tmp/sheaf/xif/paper/S2177SignQuotientDataActual.lean`
- `LeanFormal/IUT/IUTII/Frobenioid/Example36OrbicurveFeasibility.lean`
  (`MissingD6GeometricRealization`, `IsPointFiber`,
  `no_curvePointRealization_of_pointFiber`, concrete curve y^2=x^3+1)
- `LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31OrbicurveInstance.lean`
  (terminal stack, no geometry)
- `Iut/Foundations/Orbicurve.lean`
- reports `S2177-sign-quotient-xf.md`, `S2171-source-completion.md`

## Source object / domain / direction

- Source object: `MissingD6GeometricRealization A.F` with curve
  `A.curve`, i.e. the nondegenerate actual etale-stack fiber + effective
  descent + curve-point surjection.
- Domain: original O-layer, no SourceCompletion/FirstMissing assumption.
- Direction: fix the curve to `A.curve`, expose the exact fiber and
  curve-point components, and rule out terminal/degenerate point fibers.

## Deliverable

`tmp/sheaf/xif/paper/S2188D6RealizationActual.lean`

```text
EXIT=0
olean=YES
lines=114
SHA256=AA36BF9631982798880A35E217C99AAB05FC98F5186EB69CD0AC9A2DA1EA4FDE
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2188D6RealizationActual.olean
axioms: propext, Classical.choice, Quot.sound
```

## BUILT

1. `S2188D6Realization A`:
   `fiber : Iut.EtaleStackPseudofunctor A.F`,
   `isStack : fiber.IsStack (Iut.SchemeOverField.etaleTopology A.F)`,
   `nondegenerate : ¬ IsPointFiber fiber`,
   `curvePointRealization : ∃ f : fiber.obj base → A.curve.curve.toProjective.Point,
     Function.Surjective f`.
2. `s2188D6RealizationOfS2177` / `s2188S2177OfD6Realization`:
   exact equivalence with `S2177ActualD6Orbicurve A`.
3. `s2188D6Realization_iff_s2177`:
   `Nonempty (S2188D6Realization A) ↔ Nonempty (S2177ActualD6Orbicurve A)`.
4. `S2188EtaleStackFiberRequired F`: the fiber component
   (non-point fiber + IsStack).
5. `s2188EtaleStackFiberOfD6`: D6 carrier -> fiber component.
6. `s2188_terminal_fiber_forbidden`: a D6 carrier's fiber is not the
   terminal constant fiber.
7. `S2188EtaleStackFiberRequiredProp F :=
   Nonempty (S2188EtaleStackFiberRequired F)`, with definitional iff.

No inhabitant of the D6 carrier or the fiber component is asserted.

## Exact first missing

```text
S2188D6Realization A
  = fiber : Iut.EtaleStackPseudofunctor A.F
  × isStack : fiber.IsStack (Iut.SchemeOverField.etaleTopology A.F)
  × nondegenerate : ¬ IsPointFiber fiber
  × curvePointRealization :
      ∃ f : fiber.obj (baseSchemeObject A.F) →
            A.curve.curve.toProjective.Point,
        Function.Surjective f
```

Equivalently, the first missing is the pair:

```text
S2188EtaleStackFiberRequired A.F
  (actual nondegenerate etale stack fiber + effective descent)
+ curve-point surjection for A.curve
```

There is no construction of `Iut.EtaleStackOverField` with nontrivial
geometry in the tree or Mathlib 4.32.2. The terminal constant stack has
`orbicurveSignature = none`; the point fiber cannot surject onto a curve with
at least two distinct projective points (existing theorem
`no_curvePointRealization_of_pointFiber`). The concrete curve
`y^2=x^3+1` with points origin and (2,3) supplies the non-point target, but
not the stack fiber.

## Rejected fake routes

- Terminal constant fiber / sourceStackPoint fiber: point fibers, forbidden by
  `nondegenerate`; terminal also has no `OrbicurveGeometry`.
- Inserting `orbicurveSignature := some sourceTypeOneOne` into a point fiber:
  metadata-only, no geometric realization; not used.
- An arbitrary `EtaleStackPseudofunctor` with a claimed `IsStack` field:
  no such `IsStack` inhabitant is available; fields are not fabricated.

## Why not constructed

- `EtaleStackOverField` requires an actual pseudofunctor to `Cat` satisfying
  Mathlib's effective-descent predicate `Pseudofunctor.IsStack`; Mathlib
  supplies only the bare class, no bridge from a representable/scheme functor.
- The tree has only terminal/point fibers; its D6 feasibility file records
  `MissingD6GeometricRealization` with no inhabitant.
- No actual nondegenerate etale stack over an arbitrary `A.F` is constructed.

## Consumer

An inhabitant of `S2188D6Realization A` gives
`S2177ActualD6Orbicurve A`, hence xF/xF_geometry, the
`SourceSignQuotientData` prefix, and eventually SourceCompletion/native
source. No 3.11/Eta assumption.

## Next executable subgoal

```text
construct fiber : Iut.EtaleStackPseudofunctor A.F
with fiber.IsStack (Iut.SchemeOverField.etaleTopology A.F)
and ¬ IsPointFiber fiber
```

then the curve-point surjection for `A.curve`. This is the unresolved D6
geometric realization, not a signature insertion.

## Reports read

`coord/reports/S2177-sign-quotient-xf.md`,
`coord/reports/S2171-source-completion.md`, and the D6 feasibility/terminal
stack audits above.
