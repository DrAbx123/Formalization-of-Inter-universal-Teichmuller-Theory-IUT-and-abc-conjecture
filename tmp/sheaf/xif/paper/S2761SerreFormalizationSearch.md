# S2761 — Lean/Serre open-image formalization search

Date: 2026-11-07. Search evidence and curve-choice conclusion.

## 1. GitHub API search

- `https://api.github.com/search/repositories?q=serre+open+image+lean`
  returned `total_count = 0`, items = [] (HTTP 200).
- A follow-up elliptic-curve/Galois-representation repo query hit GitHub
  unauthenticated rate limit (HTTP 403), no results obtained.
- No Lean repository named/formulated as Serre open image was found.

## 2. Local Mathlib search

grep in `.lake/packages/mathlib/Mathlib` for `Serre open image` / `Serre.*image`
finds only `Mathlib/CategoryTheory/Abelian/SerreClass/*` (unrelated).
No elliptic-curve Serre open-image theorem, no large-image theorem, no
11a1-specific curve or mod-l image computation.

## 3. Local repo search

`SerreStyleLargeImageStatement` appears only as:

- a Prop definition in `SourceTorsionCarrierReduction.lean:298`;
- conditional/equivalence reductions (`S1725SourceTorsionFPrimeActual`,
  `S1987D5LargeImageFiveActual`);
- audit notes.

No theorem proves the statement for a concrete curve.

## 4. Exact gap

```text
GAP: no Lean formalization of Serre open image, and no concrete curve proof of
  exists basis, SL2(F_l) <= range(galoisLTorsionMatrixRepresentation E l basis).
```

Two possible routes:

1. Formalize the general Serre open-image theorem for non-CM E/Q without
   rational l-isogeny (large research project; not in Mathlib).
2. For 11a1, l=5: construct explicit 5-torsion basis, compute the mod-5 Galois
   action, and prove SL2(F5) containment by finite group computation.  This
   needs division-polynomial/root/Galois-action API absent from Mathlib.

## 5. Back to 11a1 curve choice

11a1 remains the best concrete choice:

- smallest conductor (11), minimal discriminant -11^5;
- non-CM (j = -2^12*31^3/11^5 not integral);
- no rational 5-isogeny, so Serre large image is true at l=5;
- curve/target statement already actual in S2760.

Alternatives:

- 14a1/15a1/17a1 etc: larger conductor, no repo/Mathlib data; not easier.
- CM curves (j=0/1728): violate large image; excluded.
- S1667/S1720 Legendre curve: has project data but no actual large-image
  theorem; S1987 is only a Prop/equivalence, not a proof.

Therefore keep 11a1 as the curve; the blocker is the missing Serre/mod-5
representation API, not the curve choice.  No curve substitution avoids the gap.

## 6. Verdict

- No existing Lean formalization found (GitHub search 0; Mathlib unrelated).
- Precise gap recorded above.
- Keep 11a1; do not claim Serre large image.  Next actual step would be a new
  mod-5 torsion/Galois API, not a different curve.