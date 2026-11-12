# S2039: [AbsTopIII] Cor 1.10(b) actual PsiCns — first-missing chain

Date: 2026-11-02. Layer: O; consumer: [AbsTopIII] Cor 1.10(b) / S2011.

## Source object

PsiCns(G_v) = lim over open U of H^1(U, mu_hat^Z(G_v)) (continuous Galois
cohomology), identified with O^tri_{F_v}, with cyclotome/Kummer image
comparison.  NOT IndIntegralMonoid/SourceMLF/PsiCnsModel.

## Domain / Direction

Domain: G_v = Gal(Qbar_p/Q_p), open subgroups U, continuous cochains with
coefficients mu_hat^Z.  Direction: actual construction and identification
maps, not a model equivalence and not a wrapped Nonempty.

## BUILT (actual, in tree)

- S2017: transfer/Verdier package, colimit muQZ p over open subgroups with
  transfer transition maps, muHatZ p = KummerCyclotome (Multiplicative (muQZ p)),
  cocone maps and universal property;
- S2024: LocalReciprocityData interface; reduction of muQZComparison and
  muHatComparison to that data; fixed-field/root-of-unity torsion maps;
- S2027: L^ab for one finite L/Q_p as fixed field of the closed commutator,
  Gal(L^ab/L) ~= TopologicalAbelianization Gal(Qbar_p/L), mu(L)=torsion L^x,
  norm of roots of unity is torsion.
- S2026/S2024: abstract local reciprocity/Artin interface, not inhabited.

## PROVED

- M1: the transfer/colimit object muQZ and dual muHatZ are actual.
- The reductions S2024/S2027 from local reciprocity data to muQZComparison and
  muHatComparison are actual.

## MISSING (exact first chain)

(M2a) localArtinTorsion U:
  Nonempty (mu U ~= torsion (Gal(L^ab/L))) for each finite L/Q_p.
  No local Artin/reciprocity map, norm limitation theorem, or local existence
  theorem in Mathlib v4.32.2; S2027 localizes this as the first missing object.

(M2b) transfer compatibility: under M2a, Verlagerung corresponds to the
  inclusion of roots of unity of fixed fields.

(M3) continuous H^2 theory and identification
  H^2(G_v, mu_hat^Z) ~= Zhat (Tate duality/local class field theory).

(M4) normalized surjection H^1 -> Zhat, and the actual limit
  PsiCns(G_v) = lim H^1(U, mu_hat^Z).

(M5) identification PsiCns(G_v) ~= O^tri_{F_v}, and cyclotome/Kummer image
  comparison.

The first missing actual lemma is M2a (localArtinTorsion); without it the
H^1/H^2 constructions cannot be normalized or identified with O^tri.

## Why no Lean file

An actual PsiCns object requires continuous group cohomology of G_v, the
local Artin map, and H^2 duality; none is in Mathlib v4.32.2 or the tree.
Writing PsiCns as IndIntegralMonoid/SourceMLF or as a Nonempty/Prop card is
the explicitly forbidden model substitution.  The exact first missing chain
is recorded instead; no fake.

## Consumer

[AbsTopIII] Cor 1.10(b), via S2011/S2017 comparisons; downstream IUT
Theta-link/cyclotome readout.

## Reports read

- tmp/sheaf/xif/paper/S2017VerlagerungActual.lean
- tmp/sheaf/xif/paper/S2024LocalReciprocityActual.lean
- tmp/sheaf/xif/paper/S2027LocalArtinActual.lean
- tmp/sheaf/xif/paper/S1973PsiCnsActual.md (model, rejected)

## Conclusion

- BUILT: M1 transfer/colim muQZ/muHatZ; S2027 L^ab; reductions.
- PROVED: actual reductions to local reciprocity data.
- MISSING first: localArtinTorsion (M2a), then transfer compatibility, H^2,
  normalized H^1->Zhat, PsiCns~=O^tri.
- No actual PsiCns/O^tri identification; no fake model; report EXIT=0.

## Lean interface file (EXIT=0)

tmp/sheaf/xif/paper/S2039ActualPsiCnsInterface.lean
SHA256 BA6BC5CE475AC80C2D25C8A4B5A3E268CB60701B329B9652A4366009C5A395F7

.lake/build/lib/lean/tmp/sheaf/xif/paper/S2039ActualPsiCnsInterface.olean
SHA256 16BFADAB8D977CC1CD5EAA278D7E2321143D5AB5BC942801E2CFE4425A55D5C0
size 63816

It imports S2027 and exposes:
- S2039FirstMissing := localArtinSourceDataMissing;
- S2039_muQZ_muHat_of_source: LocalArtinSourceData + transfer compat ->
  muQZComparison and muHatComparison;
- S2039_localArtinTorsion_of_source: levelwise localArtinTorsionTopological.

No PsiCns model or inhabitant is fabricated.
