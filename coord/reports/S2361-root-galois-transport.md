# S2361: root/Galois transport status

Date: 2026-11-03. Layer O; consumer S2352/S2217.

## No new closed Lean file

The two claimed rfl lemmas were not reproduced under the current imports and
local instance setup.

1. ambient compatibility

  algebraMap O_L L (sigma • alpha) = sigma (algebraMap O_L L alpha):

with (`local instance : MulSemiringAction Gal(L/K) O_L :=
  IsIntegralClosure.MulSemiringAction O_K K L O_L`),
`rfl` fails; the two sides are not definitionally equal.  Previous
`change`/`dsimp` attempts also fail, so the smul used by the notation is not
the normal form `galRestrict A K L B sigma alpha`.

2. root transport

  ((s2345RootSetEquiv f hmonic).symm
    (rootPerm K L f hsplit sigma ((s2345RootSetEquiv f hmonic) a))).1
    = sigma • a.1

was not reached because the O_L action statement itself is not normalized.
Also the S2167 `rootPerm` universe is fixed at `Type`, so the ambient
variables must be specialized to `K L : Type` (not `Type*`).

## Exact first missing

Identify the actual `MulSemiringAction`/`SMul` instance selected by the
notation and prove

  s2361_smul_eq_galRestrict:
    sigma • alpha =
      (galRestrict (RingOfIntegers K) K L (RingOfIntegers L)) sigma alpha

or prove the reducible compatibility directly from the chosen action's
definition (e.g. `MulSemiringAction.compHom` smul lemma).

Once this is available, `algebraMap_galRestrict_apply` gives the ambient
compatibility, and the root transport should follow by `Subtype.ext` +
`s2345RootSetEquiv_apply`.

## Actual upstream

S2345RootSetEquiv:
  f.rootSet O_L ~= (s2345P f).rootSet L,
  and it commutes with algebraMap O_L L by rfl.

## Conclusion

- BUILT: S2345 root equivalence.
- MISSING: the actual O_L smul instance normalization; then the two rfl
  lemmas, arithFrobAt compatibility, factor multiset.
- no fake; no false S2057 data.
