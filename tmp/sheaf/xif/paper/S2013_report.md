# S2013 report: S2008RootHomSheaf proved; the root prestack is a prestack

Date: 2026-11-01.  File: `tmp/sheaf/xif/paper/S2013RootHomSheafActual.lean`.

## Verdict

`S2008RootHomSheaf` is **proved**, hence (by S2008's `S2008isPrestack_iff`)

    (S1997RootPrestack K l).IsPrestack (Iut.SchemeOverField.etaleTopology K)

for every field `K` and every `l : PrimeGeFive`, unconditionally, and the exact
`IsStack` gap of S2008 is now closed on the descent-of-morphisms side:

    S2013isStack_iff : IsStack ↔ S1997RootEffectiveDescent K l.

EXIT=0, no `sorry`/`admit`/new axiom; every `#print axioms` gives only
`propext`, `Classical.choice`, `Quot.sound`.

## What is proved (unconditional, kernel-checked)

1. `S2013A1Ring`, `S2013A1`: the affine line `Spec Z[t]` at universe `u`
   (`ℤ[t] = MvPolynomial PUnit (ULift ℤ)`).

2. `S2013sectionsEquiv`, `S2013sectionsEquiv_natural`, `S2013sectionsIso`:
   **`Gamma(-, O) ≅ Hom(-, A1)`** as type valued presheaves on schemes, using
   Mathlib's `AlgebraicGeometry.AffineSpace.toSpecMvPolyIntEquiv` at
   `n = PUnit` and the generated naturality lemma
   `toSpecMvPolyIntEquiv_comp` (`(f ≫ g) ↦ f.appTop`).

3. `S2013sections_isSheaf` (**M1**): `Gamma(-, O)` is a sheaf for
   `AlgebraicGeometry.Scheme.etaleTopology`, because that topology is
   subcanonical (`Subcanonical.of_le etaleTopology_le_proetaleTopology`,
   `proetaleTopology.Subcanonical`) and `Gamma(-,O)` is representable.

4. `S2013Γ`, `S2013Γcomp`, `S2013Γ_eq_comp` (`rfl`), `S2013Γ_isSheaf`:
   on the over-site `(Over S)ᵒᵖ` the presheaf
   `T ↦ Gamma(T.left.left, O)` is a sheaf for `(etaleTopology K).over S`,
   by applying `Functor.op_comp_isSheaf_of_isSheaf` twice along the continuous
   forgetful functors `Over S ⥤ Over (Spec K) ⥤ Scheme`.

5. `S2013Γ_ext`: local characterisation of equality of sections
   (`Presieve.IsSeparatedFor.ext` for the sections sheaf).

6. `S2013units`, `S2013units_isSheaf` (**M2**): the presheaf of units
   `T ↦ Gamma(T.left.left, O)^×` is a sheaf.  A compatible family of units is
   glued by gluing the underlying sections and the sections of the inverses
   (`S2013_appTop_units_inv`, from `Units.coe_map_inv`), the product being
   `1` because it is so locally.

7. `S2013x`, `S2013y`, `S2013x_natural`, `S2013y_natural`: the sections
   `M.b`, `N.b` pulled back to a test object, natural in the test object
   (`Over.w` + `Scheme.Hom.comp_appTop`).

8. `S2013presheafHom_isSheaf` (**M3**, the main theorem):
   `Presheaf.IsSheaf ((etaleTopology K).over S) ((S2008PF K l).presheafHom M N)`
   for all `S`, `M`, `N` and all `l : Nat`.  Proof:
   * separation: `S1997RootHom.ext` reduces to the unit components;
     `S2013_zeta_restrict` (`S2008pullHom_zeta` applied to an amalgamation)
     plus `S2013Γ_ext` gives equality;
   * existence: the unit components form a compatible family of units, glued
     to `zeta : Gamma(X,O)^×` by `S2013units_isSheaf`; `zeta ^ l = 1` and
     `N.b = zeta * M.b` are checked locally with `S2013Γ_ext` and
     `x f hf |>.zeta_pow`/`x f hf |>.eq`; the resulting root hom is an
     amalgamation by `S1997RootHom.ext` again.

9. Targets: `S2013RootHomSheaf_holds : S2008RootHomSheaf`,
   `S2013RootPrestackIsPrestack : S2008RootPrestackIsPrestack`,
   `S2013RootPrestack_isPrestack : (S1997RootPrestack K l.value).IsPrestack ...`,
   `S2013isStack_iff` (`S2008isStack_iff_effDescent` applied to 9).

## Boundary / what remains

`S1997RootEffectiveDescent K l` (effective descent for the root prestack) is
**not** proved here and is *expected to fail* for Kummer covers (S2002).  What
changed is that it is now the *only* input: `S2013isStack_iff` states
`IsStack ↔ S1997RootEffectiveDescent` with no side conditions.

## Side effect

The file registers the global instance
`AlgebraicGeometry.Scheme.etaleTopology.Subcanonical` (S1421 had it only
`local`).  It is a theorem (`Subcanonical.of_le etaleTopology_le_proetaleTopology`),
so it is not an extra assumption.

## Evidence

- Build: `lake env lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S2013RootHomSheafActual.olean tmp/sheaf/xif/paper/S2013RootHomSheafActual.lean`
- EXIT=0 after a clean rebuild; wall time ≈ 36 s; no warnings.
- Source: 16499 bytes, SHA256 `7DAF97F23B4FDD4E9E69760D294D671CED409DEE99703C26AC732C6D361FF875`.
- Olean: 793520 bytes, SHA256 `9688B909BEF4F1E8140F47CDA2F0D9B55D7F24FA6E80BA7A3CB799849A5B1279`.
- `#print axioms` for `S2013sections_isSheaf`, `S2013Γ_isSheaf`,
  `S2013units_isSheaf`, `S2013presheafHom_isSheaf`, `S2013RootHomSheaf_holds`,
  `S2013RootPrestack_isPrestack`, `S2013isStack_iff`: all exactly
  `[propext, Classical.choice, Quot.sound]`.
- Lean 4.32.2, Mathlib v4.32.2.

## Next executable step

Only `S1997RootEffectiveDescent` remains for `IsStack`; S2002/S2010 suggest it
fails for the recorded weak data, so the next step is not to prove it but to
decide whether `S1997RootStackification` should be re-based on the
full 2-universal property (cf. S2015).
