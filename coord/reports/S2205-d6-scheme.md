# S2205: concrete nondegenerate scheme model; general D6 still missing

Date: 2026-11-02. Layer: **O** (source orbicurve D6). No target change,
no fake, independent of 3.11/Eta.

## Files read

- `tmp/sheaf/xif/paper/S2199RepresentableStackActual.lean`
- `tmp/sheaf/xif/paper/S1419D6NonterminalStackActual.lean`
- `tmp/sheaf/xif/paper/S1319OrbicurveClauseActual.lean`
  (`S1319NonterminalFiber`)
- `tmp/sheaf/xif/paper/S1348D6OrbicurveActual.lean`
- `tmp/sheaf/xif/paper/S2193D6RealizationModelActual.lean`
- reports `S2199-representable-stack.md`, `S2188-d6-realization.md`

## Source object / domain / direction

- Source object: `S2199D6Remaining A` for the paper arithmetic field/curve.
- Domain: original O-layer; no SourceCompletion/FirstMissing assumption.
- Direction: test a concrete actual scheme X, prove nondegeneracy and IsStack,
  and isolate the remaining curve-point realization.

## Deliverable

`tmp/sheaf/xif/paper/S2205D6SchemeActual.lean`

```text
EXIT=0
olean=YES
lines=81
SHA256=67E75833866E587011A7393971A24652732A93F188A8453336D2BD1A962F0E76
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2205D6SchemeActual.olean
axioms: propext, Classical.choice, Quot.sound
```

## BUILT / PROVED (actual)

1. `s2205_concrete_model_nondegenerate`:
   `¬ IsPointFiber (schemeRepresentableEtalePseudofunctor (S1348K l)
      (S1419AffineOver l))`.
   Uses the actual S1419 two-section argument: the S1419 affine Gaussian scheme
   has two distinct algebra points, hence two distinct sections over the base
   test object; its representable fiber is not a point fiber.
2. `s2205_concrete_model_isStack`: the same representable fiber is an etale
   stack (S2199).
3. `S2205D6SchemeRequired A := S2199D6Remaining A`.
4. `s2205D6RealizationOfScheme`: a general scheme datum gives
   `S2188D6Realization A`.
5. `S2205D6SchemeRequiredProp A`, definitional iff.

No inhabitant of the general scheme datum is asserted.

## What is closed

- representable fiber `IsStack` for all schemes over F (S2199);
- **nondegeneracy for the concrete S1419 affine Gaussian model** over
  `S1348K l`: actual, via two distinct algebra points.

## Exact first missing (general paper A.F / A.curve)

```text
S2199D6Remaining A
  = scheme : Iut.SchemeOverField A.F
  × nondegenerate :
      ¬ IsPointFiber (schemeRepresentableEtalePseudofunctor A.F scheme)
  × curvePointRealization :
      ∃ f : (schemeRepresentableEtalePseudofunctor A.F scheme).obj
            (LocallyDiscrete.mk (Opposite.op (baseSchemeObject A.F)))
            → A.curve.curve.toProjective.Point,
        Function.Surjective f
```

The concrete S1419 model does **not** solve this for arbitrary A.F:

- its field is the fixed `S1348K l`, not arbitrary `A.F`;
- its affine Gaussian scheme is not the paper `A.curve`;
- its F-points are not identified with the projective points of `A.curve`;
- the paper curve may have projective points not represented by an affine
  Weierstrass scheme (puncture/point at infinity).

Therefore the exact first missing is still a scheme X over the paper A.F
together with nondegeneracy and an actual surjection from X-points onto
`A.curve.curve.toProjective.Point`.

No equality of fields/curves or curve-point map was fabricated.

## Rejected routes

- terminal/point fibers: excluded by nondegeneracy and the two-point argument;
- metadata signature insertion: not a geometric realization;
- S1419 concrete model substitution for arbitrary A.F/A.curve: different
  field and curve; not used;
- disjoint-union/coproduct of points as a D6 scheme: would satisfy the raw
  surjection only by discarding geometric realization; not used.

## Consumer

A general `S2205D6SchemeRequired A` gives `S2188D6Realization A`, hence
`S2177ActualD6Orbicurve A`, `xF`/`xF_geometry`, and the
`SourceSignQuotientData` prefix. No 3.11/Eta assumption.

## Next executable subgoal

```text
choose actual X : SchemeOverField A.F
prove ¬ IsPointFiber (representable fiber X)
and construct X(A.F) ↠ A.curve.curve.toProjective.Point surjective
```

A first substep is to prove nondegeneracy for a concrete scheme over arbitrary
A.F (two distinct A.F-points); the curve-point surjection remains the hard
projective/root-stack model field.

## Reports read

`coord/reports/S2199-representable-stack.md`,
`coord/reports/S2188-d6-realization.md`, and the S1419 nonterminal-stack
construction.
