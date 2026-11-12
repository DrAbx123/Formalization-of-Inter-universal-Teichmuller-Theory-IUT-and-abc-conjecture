# S1852 CoherentCover / StrongCover vs S1728Cover

Date: 2026-11-06. Source: tmp/sheaf/xif/paper/S1852CoherentCoverActual.lean
src SHA256 50D415E1DA8D3D46F8808DD48806E6F283A170ECC29D7C43C51821131F3FB429; olean exists=true size=453272

## Relation table

| Object | Role | Relation to S1728Cover |
|---|---|---|
| S1728Cover | recorded orbicurve finite-etale cover | base object |
| StrongCover X | structure extending a cover with finite-etale/2-universal strength | `StrongCover.cover : S1728Cover` (forgetful) |
| CoherentCover | `extends StrongCover S1726Orbicurve` + `unit : S1756Unit cover` | `CoherentCover.cover = StrongCover.cover`; forgets to S1728Cover |

## Is every paper cover coherent? NO

The file proves a concrete counterexample:

- `S1852DoubledCover_not_coherent (C : CoherentCover)
    (hC : C.cover = S1850DoubledCover) : False`
  i.e. the S1850 doubled cover is NOT the underlying cover of any CoherentCover.
- `S1852Doubled_not_strong`: no StrongEtaleStackFiniteEtaleMorphism forgets to
  S1850DoubledFiniteEtale.
- `S1852DoubledIdentity_not_coneEssSurj`: the doubled presentation lacks the
  full 2-universal property.

## Coherence implications

- `CoherentCover.ofStrong : StrongCover S1726Orbicurve -> CoherentCover`
  (strong + unit gives coherent).
- `S1852CoherentNonempty`: a terminal coherent cover exists.
- `S1852ConeEssSurj_of_coherent`: coherent cover has cone essential surjectivity.
- `∀ A : S1728Cover, ∃ C : CoherentCover, C.cover = A` is an explicit hypothesis,
  NOT a theorem; it would give `S1756FirstMissing`.

## Conclusion

StrongCover/CoherentCover are strict strengthenings of the S1728 cover datum,
not properties enjoyed by every cover. The doubled S1850 cover is the concrete
obstruction. Therefore the answer to 'is every paper cover coherent?' is NO.

