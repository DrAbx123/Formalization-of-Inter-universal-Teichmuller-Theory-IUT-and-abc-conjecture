# S2040 P1: finite unramified L/Q_p Artin torsion — exact first missing

Date: 2026-11-02. Layer O; consumer S2039 M2a / [AbsTopIII] Cor 1.10(b).

## Target P1

For finite unramified L/Q_p, construct the local Artin map via Frobenius and
the torsion identification

  mu(L) = torsion (L^x) ~= torsion (Gal(L^ab/L)),

plus unramified norm compatibility.

## Actual available

- S2027: L^ab as fixed field of the closed commutator;
  TopologicalAbelianization Gal(Qbar_p/L) ~= Gal(L^ab/L);
  mu(L) = torsion L^x; exact Props localArtinTorsion and
  localArtinTorsionTopological; reductions to S2024/S2017 when the datum is
  supplied.
- Mathlib has residue-field Frobenius and finite Galois theory of residue
  fields, and abstract profinite completions.

## Why P1 is not constructible from the tree

Even in the unramified case the required map is not the residue Frobenius:
the torsion of Gal(L^ab/L) is the image of the local Artin map on roots of
unity, which lies in the inertia/cyclotomic direction.  Constructing it needs:

1. the maximal unramified extension L^ur as a field and its Frobenius;
2. the unramified local Artin map Gal(L^ur/L) -> Z-hat;
3. the cyclotomic character on inertia and the identification of the
   p'-primary roots of unity mu(L) with the corresponding quotient of
   Gal(L^ab/L);
4. norm compatibility for unramified subextensions.

Mathlib v4.32.2 has no local Artin/reciprocity map, no norm limitation
theorem, no local existence theorem, and no construction of L^ur as an
infinite unramified extension with Frobenius.  The discrete-valuation file
only references external local class field theory.

Thus P1's exact first missing object is the unramified local Artin map

  rec_ur : Gal(L^ur/L) ->* Zhat

together with the cyclotomic/torsion identification

  mu(L) ~= torsion (Gal(L^ab/L)).

Equivalently, an inhabitant of S2027's exact Prop

  localArtinTorsionTopological p U

for the levels U corresponding to finite unramified L/Q_p.  No inhabitant is
fabricated.

## Minimal reusable interface

The existing S2039ActualPsiCnsInterface.lean already provides the exact
interface:

  S2039FirstMissing := localArtinSourceDataMissing p
  S2039_localArtinTorsion_of_source
  S2039_muQZ_muHat_of_source

and S2027 provides localArtinTorsionTopological, LocalArtinSourceData, and
the reductions.  A P1-specific file would only restate these Props; it would
not be a construction.

## Conclusion

- actual: L^ab, profinite abelianization, mu(L), reductions.
- exact first missing P1: unramified local Artin map rec_ur and the
  cyclotomic/torsion identification; equivalently inhabitant of
  localArtinTorsionTopological for unramified levels.
- no fake/axiom/Nonempty wrapper; no IndIntegralMonoid/SourceMLF model.
- report EXIT=0.
