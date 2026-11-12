# S2212: general D6 scheme reduced to two sections + curve-point realization

Date: 2026-11-02. Layer: **O** (source orbicurve D6). No target change,
no fake, independent of 3.11/Eta.

## Files read

- `tmp/sheaf/xif/paper/S2205D6SchemeActual.lean`
- `tmp/sheaf/xif/paper/S2199RepresentableStackActual.lean`
- `tmp/sheaf/xif/paper/S1419D6NonterminalStackActual.lean`
- `tmp/sheaf/xif/paper/S2188D6RealizationActual.lean`
- `Iut/Foundations/Orbicurve.lean`
- reports `S2205-d6-scheme.md`, `S2199-representable-stack.md`

## Source object / domain / direction

- Source object: `S2199D6Remaining A` for arbitrary paper field/curve.
- Domain: original O-layer; no SourceCompletion/FirstMissing assumption.
- Direction: eliminate the nondegeneracy field using two distinct A.F-sections,
  and isolate the remaining actual scheme + curve-point realization.

## Deliverable

`tmp/sheaf/xif/paper/S2212D6GeneralSchemeActual.lean`

```text
EXIT=0
olean=YES
lines=90
SHA256=DDC1CC51EB81FE7B577C19A84A127DF718B9E05F54679D4300B2C0986F3BC0FF
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2212D6GeneralSchemeActual.olean
axioms: propext, Classical.choice, Quot.sound
```

## BUILT / PROVED (actual)

1. `S2212TwoPointScheme A`:
   `X : SchemeOverField A.F`,
   `s1 s2 : baseSchemeObject A.F ⟶ X`,
   `s1 ≠ s2`.
2. `s2212_twoPoint_nondegenerate`:
   two distinct sections imply
   `¬ IsPointFiber (schemeRepresentableEtalePseudofunctor A.F X)`.
   Proof: if the fiber at the base test object were a subsingleton, the two
   sections (elements of the discrete representable fiber) would be equal.
3. `S2212GeneralD6Scheme A`: two-point scheme plus
   `curvePointRealization`:
   `∃ f : representable fiber at base → A.curve.curve.toProjective.Point,
     Surjective f`.
4. `s2212D6RemainingOfGeneral`: such data gives `S2199D6Remaining A`
   (nondegeneracy is now a theorem, not a field).
5. `S2212GeneralD6SchemeRequired A := Nonempty (...)`, with definitional iff.

No inhabitant of the general scheme datum is asserted.

## Exact first missing

```text
S2212GeneralD6Scheme A
  = X : Iut.SchemeOverField A.F
  × s1 s2 : baseSchemeObject A.F ⟶ X
  × (s1 ≠ s2)
  × ∃ f : (schemeRepresentableEtalePseudofunctor A.F X).obj
          (LocallyDiscrete.mk (Opposite.op (baseSchemeObject A.F)))
          → A.curve.curve.toProjective.Point,
      Function.Surjective f
```

The nondegeneracy component is now constructible from two actual sections.
The remaining hard components are:

1. an actual `X : SchemeOverField A.F` with two distinct A.F-points;
2. a surjection from `X(A.F)` onto the projective points of the paper curve
   `A.curve`.

No such `X` is chosen/constructed here.

## Why affine Weierstrass is insufficient

An affine Weierstrass scheme can supply two rational sections (e.g. points
`(0,0)`, `(1,0)` of `y^2=x^3-x`), but:

- it is not the paper `A.curve` unless the curve is identified;
- its F-points need not cover the projective points of `A.curve`;
- the puncture/point at infinity is generally not an affine section;
- no actual projective/root-stack model realizing all projective points over
  arbitrary A.F is constructed in the tree.

A disjoint union of point schemes would satisfy the raw surjection only by
discarding the geometric realization, and is not used.

## Rejected routes

- terminal/point fibers: excluded by the two-section theorem;
- S1419 concrete model: field `S1348K l` and curve not `A.curve`;
- metadata signature: no geometric content;
- artificial coproduct of points: not a paper curve realization;
- declared `IsStack` or nondegeneracy fields: not done.

## Consumer

`S2212GeneralD6Scheme A` -> `S2199D6Remaining A` ->
`S2188D6Realization A` -> `S2177ActualD6Orbicurve A` ->
`xF`/`xF_geometry` -> `SourceSignQuotientData` prefix. Independent of
3.11/Eta.

## Next executable subgoal

```text
construct X : SchemeOverField A.F with two distinct A.F-points
and a surjection X(A.F) ↠ A.curve.curve.toProjective.Point
```

A first substep is to construct the two sections for a candidate X; the
curve-point surjection needs an actual projective/root-stack model.

## Reports read

`coord/reports/S2205-d6-scheme.md`,
`coord/reports/S2199-representable-stack.md`, plus S1419 nonterminal stack.
