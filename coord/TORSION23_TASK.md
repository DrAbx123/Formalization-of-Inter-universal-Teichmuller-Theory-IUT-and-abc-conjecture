# Torsion23Rational for F6 — finish

Lean 4.32.2 + Mathlib v4.32.2, D:/lean.
Goal: Torsion23Rational (S2790E.baseChange S2790F6) (S2810Torsion23Target).

Existing actual:
- S2811: F6=↥S2790F6 finite/NumberField/Normal/IsGalois
- S2812Equiv : AlgebraicClosure S2790F6 ≃ₐ[S2790F6] S2790L
- S2815 prep: hcomp, hns_align, coord_mem
- S2806 exact uniformizer; S2811CoordStableActual (S2790CoordSet stable)

Key known issue: Point.baseChange/Point.map type cast and instance diamond between
AlgebraicClosure.instField.toCommRing and AlgebraicClosure.instCommRing.
Strategy:
1. From P : (S2790E.baseChange F6).curve.toAffine.Point with 6•P=0, use S2812Equiv to get
   coordinates (x,y) of e(P) in S2790L; e(P) is 6-torsion; its coordinates lie in S2790CoordSet,
   hence in F6.
2. Construct Q : (S2790E.baseChange F6).curve.toAffine.Point from x0,y0 in F6 via
   Affine.Point.some x0 y0 hns0; prove map (Algebra.ofId F6 L1) Q = P.
3. Avoid Point.some.injEq instance mismatch: use `convert hmap using 2 <;> exact Subsingleton.elim _ _`,
   or prove equality through `Affine.Point.map_injective`? (map is injective; no inverse).
4. If Lean falls into CommRing diamond, do NOT use letI causing synthetic sorry. Instead
   define all points on the SAME curve type using `hV ▸` at the goal level, not hV.symm ▸ P.
Compile: lake env lean -j1 -R 'D:/lean' -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S2826Torsion23Fresh.olean tmp/sheaf/xif/paper/S2826Torsion23Fresh.lean
Report EXIT/first error/src-olean SHA/axioms. No sorry/extra axioms.