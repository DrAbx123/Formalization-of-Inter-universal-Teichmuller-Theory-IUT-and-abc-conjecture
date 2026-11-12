# S2039 M2a: local Artin torsion identification — exact first missing

Date: 2026-11-02. Layer O; consumer [AbsTopIII] Cor 1.10(b).

## Target

For finite L / Q_p, construct an actual multiplicative equivalence

  μ(L) = torsion (L^x)  ≃*  torsion (Gal(L^ab/L))

then the levelwise LocalArtinSourceData and M2b transfer compatibility.

## Actual available

S2027 constructs, unconditionally:

- L^ab as fixed field of the closed commutator of Gal(Qbar_p/L);
- galoisGroupMaximalAbelian:
    TopologicalAbelianization Gal(Qbar_p/L) ≃* Gal(L^ab/L);
- μ(L) = CommGroup.torsion (localField p U)^x, with injective
  muInGlobal : μ(L) ->* torsion (Qbar_p^x);
- norm of roots of unity is torsion;
- localArtinTorsion and localArtinTorsionTopological as exact Props;
- localArtinTorsion_iff_topological;
- LocalArtinSourceData with fields artin (M2a) and carrier (M2c);
- levelwiseEquiv, localReciprocityData_of_source, and
  muQZComparison_of_source / muHatComparison_of_source from the source data
  plus M2b transfer compatibility.

Thus all reductions below M2a are actual.

## Exact first missing

The missing object is the local Artin/reciprocity map

  rec_L : L^x ->* Gal(L^ab/L)

together with its torsion identification (M2a) and norm compatibility (M2b).
Equivalently, an inhabitant of

  LocalArtinSourceData p

whose first field is

  artin : forall U, μ(U) ≃* torsion (TopologicalAbelianization (Gal(Qbar_p/L_U))).

Mathlib v4.32.2 has no local Artin map, no norm limitation theorem, no local
existence theorem; the discrete-valuation file only references external local
class field theory.  The tree has no independent construction.

## Why no Lean file for M2a

Any Lean file claiming M2a must either:

- construct rec_L (local class field theory, unavailable); or
- assume LocalArtinSourceData / localArtinTorsion (forbidden fake).

Writing a new Prop/Nonempty wrapper would not advance the actual object; the
interface file S2039ActualPsiCnsInterface.lean already records the exact
missing datum without assuming it.

## Consequence

- M2a remains the first missing actual object.
- M2b, M3 H^2/Ẑ, M4 normalized H^1->Ẑ, M5 PsiCns ~= O^tri remain downstream.
- The actual reductions S2024/S2027 are verified and can be consumed once an
  actual LocalArtinSourceData + transfer compatibility are supplied.

## Conclusion

- actual: L^ab, profinite abelianization identification, μ(L), S2024/S2027
  reductions.
- exact first missing: local Artin map rec_L / LocalArtinSourceData inhabitant.
- no fake; no IndIntegralMonoid/SourceMLF model; report EXIT=0.
