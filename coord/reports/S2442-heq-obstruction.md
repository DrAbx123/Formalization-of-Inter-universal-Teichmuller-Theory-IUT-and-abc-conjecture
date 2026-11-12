# heq action-equivariance: exact obstruction

## What `heq` actually requires
S2131/S2159 define the equivariance field as:
  forall g : Gv p, forall x : muHatZ p,
    S2131ModuleEquivOfComparison h (S2159MuHatActionOfMuQZ a g x)
      = (PsiCnsCoefficientAction p).automorphism g (S2131ModuleEquivOfComparison h x),
where `h : muHatComparison p` is only a `Prop := Nonempty (muHatZ p ≃* PsiCnsTorsionCyclotome p)`.
S2046G1 `S2046G1PsiCnsAction` is the actual `PsiCnsCoefficientAction.automorphism`, and `S2131ModuleEquivOfComparison h` is `S2046G1ModuleEquivOfComparison h = Classical.choice (PsiCnsCyclotome_equiv_of_cyclotomeComparison p h)`.
S2442MuQZAction acts on `muQZ`; `S2159MuHatActionOfMuQZ` turns it into an action on `muHatZ` by precomposition.

## First obstruction: non-canonical choice
`muHatComparison` is a bare existence proposition. `S2131ModuleEquivOfComparison h` chooses an arbitrary equivalence via `Classical.choice`. The equivariance equation is not a property of an arbitrary chosen equivalence; a different choice can conjugate the action by an automorphism of `muHatZ` and destroy the square unless the comparison is canonical and natural. Therefore `heq` cannot be derived from `h : muHatComparison` alone.

## Second obstruction: the canonical comparison is exactly muQZComparison
A canonical equivariant comparison would have to be built from the local Artin map on torsion units, i.e. it requires the actual `muQZComparison` (or a canonical `muHatComparison` with its naturality data). But `muQZComparison` is blocked by the kappa/Verlagerung naturality square:
  torsionMap (kappa H) (torsionMap (verlagerungOpen h) v)
    = torsionMap (verS2027 h) (torsionMap (kappa K) v).
No such theorem is available. Hence the canonical comparison and its equivariance are blocked at the same point.

## Explicit formula attempt
At the generator level, `S2442MuQZAction_compat` gives
  toAdd (S2442MuQZAction g (ofAdd (muQZof H v)))
    = muQZof (S2169ConjIndex g^-1 H) (S2179StageConj g^-1 H v).
`PsiCnsCoefficientAction` is the action on `Hom(Q/Z, (Otri)^x)` by postcomposition with the integral unit action. To compare these formulas, one must identify `muQZof` generators with `PsiCnsCyclotome` functions via a canonical local-Artin comparison. Without that identification, there is no common carrier on which the formula can be checked.

## Exact first missing
1. A canonical (not `Classical.choice`-arbitrary) local-Artin comparison `muQZ p -> Additive (torsion (Otri p)^x)` or `muHatZ p ≃* PsiCnsTorsionCyclotome`;
2. its naturality with `kappa`/Verlagerung (the kappa-transfer square);
3. only then the generator-wise action square `heq`.
This is not an interface-only gap: no inhabitant of the canonical comparison is constructed.

## Consequence for EndComm
Without heq, `muHatComparison` alone does not give `S2432EndComm`; the literal S2189 route remains:
  canonical muQZComparison -> heq -> S2432EndComm -> literal S2189.
No actual/refutation of EndComm is produced here.

## Status
No new Lean file compiled; no build/cache command; no fake/axiom/interface file. Exact obstruction: non-canonical `Nonempty` comparison and missing kappa-transfer naturality.