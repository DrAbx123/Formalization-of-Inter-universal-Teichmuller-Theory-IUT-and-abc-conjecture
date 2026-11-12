# S2822 — E37 projective point-realization route

Date: 2026-11-07. Target: compare F-points of `E37ProjGluedScheme` with
`E37.toProjective.Point`, and isolate what is needed for a surjectivity proof.
This is an executable route, not a claim that surjectivity is proved.

## 0. Objects

```lean
E37 : WeierstrassCurve ℚ
E37Qi := E37.baseChange GaussianField
E37ProjGluedScheme K e := (E37ProjGlueData K e).glued
E37ProjChartZMap : S2801E37AffineScheme K ⟶ E37ProjGluedScheme K e
E37ProjChartYMap : E37ChartYScheme K ⟶ E37ProjGluedScheme K e
```

`E37.toProjective.Point` is the Mathlib nonsingular projective point type.

## 1. Actual cover step

`S2822PointRealizationRouteActual.lean` is ACTUAL:

```text
source A8485F9DD6816A6A796CAB67ABA638DA22C5DFE3E7F91593B45480261AD0FBE7
olean 59552 B SHA 594DA77E981FCB943DF2A060E06FF3122B541F65B14BAB6091CAF612C485FB43
axioms trio
```

It proves:

```lean
S2822_E37ProjCharts_jointly_surjective :
  forall x : E37ProjGluedScheme K e,
    (exists y, E37ProjChartZMap K e y = x) \/
    (exists y, E37ProjChartYMap K e y = x)
```

using `(E37ProjGlueData K e).openCover.exists_eq`.

## 2. Comparison path for F-points

Take an F-point as `Spec (CommRingCat.of F) ⟶ E37ProjGluedScheme F e`.

1. **Factor through a chart.** Apply the cover of §1 to the underlying point
   of the F-point, but the F-point-level factorization

```lean
S2822_fpoint_factors_chart (x : Spec (CommRingCat.of F) ⟶ E37ProjGluedScheme F e) :
  (exists z, E37ProjChartZMap F e ≫ ? = x) \/ (exists y, ...)
```

   is NOT yet actual. Need the open-immersion/cover factorization lemma: an
   F-point whose image lies in an open chart factors through that chart.
   For open immersions this should follow from the universal property of open
   subschemes; Mathlib has `Scheme.Opens`/`IsOpenImmersion.lift` machinery, but
   the exact glue-chart statement is missing.

2. **Chart-Z F-points ↔ affine Weierstrass points.**
   `S2801E37AffineScheme F = Spec (F[x,y]/(y^2+y-x^3+x))`. An F-point is a
   ring hom `E37CoordinateRing → F`, equivalently `(X,Y) ∈ F × F` satisfying
   `Y^2+Y = X^3-X`. Need:

```lean
S2822_chartZ_fpoint_equiv_affine :
  (Spec F ⟶ S2801E37AffineScheme F) ≃
    { p : F × F // p.2^2 + p.2 = p.1^3 - p.1 }
```

   using `Spec.homEquiv` / `MvPolynomial.eval`; then map to
   `E37.toAffine.Point` via the nonsingularity of the Weierstrass equation.

3. **Chart-Y F-points ↔ infinity.** The chart-Y equation is
   `s^3 - s t^2 - t - t^2`; `(s,t)=(0,0)` is the infinity point. Need:

```lean
S2822_chartY_infinity_fpoint :
  Spec F ⟶ E37ChartYScheme F  (the point at (0,0))
  maps to (0 : E37.toProjective.Point)
```

   plus the statement that chart-Y F-points used in the route are only the
   infinity/`Y=1` chart point (other chart-Y points lie in the overlap and are
   handled by chart Z).

4. **Overlap compatibility.** For an F-point in both charts, the chart-Z and
   chart-Y images in the glued scheme agree, and the two affine/projective
   readings agree. This uses the transition isomorphism `e` and the glue
   condition; no additional mathematical input.

5. **Surjectivity assembly.** Every `P : E37.toProjective.Point` is `0` or an
   affine nonsingular point (`P.toAffine`); use `Point.toAffineAddEquiv`/
   `fromAffine` to case split. Send `0` through chart Y and an affine point
   through chart Z, then apply the F-point comparison maps of steps 2-4.

## 3. Exact missing lemmas

1. `S2822_fpoint_factors_chart` — open-chart factorization of F-points.
2. `S2822_chartZ_fpoint_equiv_affine` — `Spec`-point ↔ coordinate-ring
   `F`-point ↔ affine Weierstrass point.
3. `S2822_chartY_infinity_fpoint` — infinity chart point maps to projective `0`.
4. `S2822_chart_overlap_compat` — overlap agreement of the two chart readings.

## 4. Executable plan

1. Prove `S2822_fpoint_factors_chart` first (pure open-immersion/cover lemma).
2. Prove the chart-Z affine equivalence by `Spec.homEquiv` + polynomial
   evaluation; this is the main formalization work.
3. Prove the infinity/chart-Y correspondence and overlap compatibility.
4. Assemble surjectivity by case split on `P.toAffine` (`0` vs `some`).

`S2822_E37ProjCharts_jointly_surjective` (actual) is the scheme-level input
already available; the remaining four lemmas are the F-point/Weierstrass
correspondence layer.

## 5. S2828 implementation status (2026-11-07)

File `S2828PointRealizationActual.lean` is ACTUAL (olean 107416 B,
SHA FA3A9B3405E60CA0F0D584E29DBA726A0FAD7615289AA1485C03530801DE9D85;
source SHA 7C9E42CF77EDB1F0CBE212030B12BB94738E2860CEEB1B3B205D895ECAB09A33;
axioms trio) and proves:

1. `S2828_fpoint_factors_chart` — every F-point of `E37ProjGluedScheme F e`
   factors through chart Z or chart Y (the open-immersion lift plus the actual
   `S2822_E37ProjCharts_jointly_surjective`).
2. `S2828_chartZHom` — extraction of the coordinate-ring F-point
   `S2801E37CoordinateRing F →+* F` from an F-point of the affine chart.
3. `S2828_chartZ_equation` — the extracted coordinates satisfy the E37 affine
   equation, from `S2801E37_relation`.

Remaining first errors/blockers:

- Point construction from `S2828_chartZ_equation` needs nonsingularity:
  `S2801E37Curve F` is only elliptic when `37 ≠ 0` in `F`; the exact missing
  step is an `IsElliptic` instance (char-0 or `(37 : F) ≠ 0` hypothesis) before
  `WeierstrassCurve.Affine.equation_iff_nonsingular`.
- The target `E37.toProjective.Point` is over ℚ, while the chart F-points are
  over F. There is no base-change comparison map in the current file; the
  F-point map lands naturally in `(S2801E37Curve F).toProjective.Point` (or
  `E37Qi.toProjective.Point` after base change). This is the exact carrier
  mismatch blocking a direct `S2828` surjectivity statement.
- `S2822_chartY_infinity_fpoint` and `S2822_chart_overlap_compat` need the same
  missing F-point → projective point comparison map, so they are not yet
  formalizable against the stated target.