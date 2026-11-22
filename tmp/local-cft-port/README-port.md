# Local CFT port: P0 layout and P1 Kummer build

Date: 2026-11-02.

## P0 copied sources

- local-class-field-theory-main: 106 Lean files;
  toolchain leanprover/lean4:v4.32.0;
  Mathlib rev 81a5d257c8e410db227a6665ed08f64fea08e997;
- continuous-kummer-theory-main: 19 Lean files;
  dependency of local CFT.

Current project: Lean v4.32.2, Mathlib rev 905b (project pin).

Root imports: LocalClassFieldTheory.lean imports all 106 modules.

## P1 Kummer module dependency order

1. ContinuousKummerTheory.ContH1.Basic  -- compiled EXIT=0
2. ContinuousKummerTheory.ContH1.Comparison
3. ContinuousKummerTheory.ContH1.Corestriction
4. ContinuousKummerTheory.ContH1.CorestrictionIndep
5. ContinuousKummerTheory.Hilbert90
6. ContinuousKummerTheory.Kummer.Basic
7. ContinuousKummerTheory.Kummer.Equiv
8. ContinuousKummerTheory.Kummer.Limit
9. ContinuousKummerTheory.Kummer.Restriction
10. ContinuousKummerTheory.Kummer.ZHat
11. ContinuousKummerTheory.Kummer.Corestriction
12. ContinuousKummerTheory.Kummer.CorRes
13. ContinuousKummerTheory.Kummer.ProfiniteCompletion
14. ContinuousKummerTheory.Kummer.Topology
15. ContinuousKummerTheory.Kummer.Values
16. ContinuousKummerTheory.Kummer.PAdic
17. ContinuousKummerTheory.Kummer.Specialization
18. ContinuousKummerTheory.Kummer.Decomposition
19. ContinuousKummerTheory (root)

Build command used:

  LEAN_PATH=<port-olean>;<kummer-root>;<project LEAN_PATH>
  lake env lean -j1 -R <kummer-root> -o <port-olean>/<module>.olean <file>

## P1 current status

- ContH1.Basic: compiled EXIT=0, olean 631408 bytes.
- ContH1.Comparison: blocked by a transient missing Mathlib olean.private:
  Mathlib.AlgebraicGeometry.Morphisms.Descent.olean.private
  (the file exists in the tree; another build is rewriting Mathlib oleans).
- No source compile error yet in the Kummer port; retry after the concurrent
  Mathlib build settles.

## M2a alignment

The LANA target to port is:

- PadicField.artin : K^x ->* Gal(K^ab/K)
- localArtinEquiv / NormCompat / UnramifiedZHat
- Reciprocity.ArtinInertia, ExistenceTheorem

These should supply S2027's:

- localReciprocityIsomorphism U,
- M2a-torsion torsion(L^x-hat) ~= mu(L),
- localArtinTorsion,
- M2c profiniteTorsionComparison (partly),
- M2b transfer.

No LocalArtinSourceData inhabitant is assumed or fabricated.

## Conclusion

- P0 complete: sources copied and import graph recorded.
- P1 partial: Basic compiled; full Kummer blocked by concurrent Mathlib
  olean rewrite, not by a Kummer source error.
- Next: retry Kummer chain; then port PadicField core.
