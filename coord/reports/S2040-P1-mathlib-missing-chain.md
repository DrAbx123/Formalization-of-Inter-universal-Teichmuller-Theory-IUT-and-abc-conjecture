# S2040 P1: exact Mathlib missing chain for unramified local Artin

Date: 2026-11-02. Layer O; consumer S2039 M2a / [AbsTopIII] Cor 1.10(b).

## What is actually in Mathlib v4.32.2

- cyclotomicCharacter L p : (L ≃+* L) →* Z_p^×, with spec on roots of unity
  (Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean);
- Valuation.RamificationGroup.inertiaSubgroup for a valuation subring;
- abstract profinite completion and transfer/Verlagerung (S2017);
- no local Artin map, no Lubin-Tate formal group, no local class field
  existence/norm limitation theorem, no maximal unramified extension with
  Frobenius as a topological generator.

## Missing chain (ordered)

1. A nonarchimedean local field structure for finite L/Q_p with normalized
   valuation and finite residue field.  Partial valuation API exists, but no
   bundled local-field object with the exact residue/valuation fields.
2. The maximal unramified extension L^ur inside an algebraic closure and the
   Frobenius automorphism Frob_L, with
     Gal(L^ur/L) ≃* Zhat, Frob ↦ 1.
   Mathlib has no L^ur object and no Frobenius topological generator theorem.
3. The unramified local Artin map
     rec_ur : L^× →* Gal(L^ur/L),
   normalized by rec_ur(uniformizer) = Frob_L.
   No such map exists in Mathlib.
4. The cyclotomic/torsion compatibility
     rec_L(ζ) acts on roots of unity by the cyclotomic character,
   and the resulting
     μ(L) ≃* torsion (Gal(L^ab/L)).
   cyclotomicCharacter gives the Galois side action, but there is no map from
   L^× to Gal(L^ab/L) to feed it.
5. Norm limitation and local existence (for P3), and the transfer
   compatibility (P4) between Verlagerung and fixed-field roots-of-unity
   inclusion.

## Minimal reusable interface

Already actual:

- S2027 `LocalArtinSourceData` with fields `artin` (M2a) and `carrier` (M2c);
- S2027 `localArtinTorsion`, `localArtinTorsionTopological`;
- S2027 reductions `levelwiseEquiv`, `localReciprocityData_of_source`,
  `muQZComparison_of_source`, `muHatComparison_of_source`;
- S2039ActualPsiCnsInterface.lean (EXIT=0) exposing these without inhabitant:
  S2039FirstMissing, S2039_localArtinTorsion_of_source,
  S2039_muQZ_muHat_of_source.

A P1-specific interface would need to add the missing L^ur/Frobenius/rec_ur
types; without them it would only rename M2a.  No such wrapper is written.

## Conclusion

- actual: cyclotomic character, inertia subgroup, transfer; all M2a
  reductions in S2024/S2027.
- exact first missing: `rec_ur : L^× →* Gal(L^ur/L)` with
  `Gal(L^ur/L) ≃ Ẑ` and Frobenius normalization, followed by the
  cyclotomic torsion identification.
- no fake/Nonempty wrapper; no IndIntegralMonoid/SourceMLF model.
- report EXIT=0.
