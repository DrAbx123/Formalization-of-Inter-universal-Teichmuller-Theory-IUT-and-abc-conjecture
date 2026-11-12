# S2352: Galois action compatibility status

Date: 2026-11-03. Layer O; consumer S2345/S2342.

## No new closed Lean file

Ambient compatibility

  algebraMap O_L L (sigma • alpha) = sigma (algebraMap O_L L alpha)

was not closed.  The S2345 equivalence is actual; this step is blocked on the
O_L MulSemiringAction instance/API.

## Exact first missing

Mathlib defines the Galois action on O_L as

  IsIntegralClosure.MulSemiringAction (RingOfIntegers K) K L (RingOfIntegers L)
    := MulSemiringAction.compHom B (galRestrict A K L B).toMonoidHom.

Under a local `letI` of this instance, the term `sigma • alpha` did not reduce
definitionally to

  (galRestrict (RingOfIntegers K) K L (RingOfIntegers L)) sigma alpha.

So `algebraMap_galRestrict_apply` cannot be applied directly; `change` and
`dsimp [IsIntegralClosure.MulSemiringAction, MulSemiringAction.compHom]` both
failed.  There may be another ambient `SMul`/`MulSemiringAction` instance
winning instance resolution, or the `MulSemiringAction.compHom` smul lemma has
a different normal form.

Missing API/lemma:

  s2352_smul_eq_galRestrict:
    sigma • alpha =
      (galRestrict (RingOfIntegers K) K L (RingOfIntegers L)) sigma alpha.

Once this is available,

  algebraMap_galRestrict_apply (RingOfIntegers K) sigma alpha

immediately gives the ambient compatibility.

## Next missing after that

1. A Gal(L/K)-action on `f.rootSet (RingOfIntegers L)` preserving roots, to
   state
   s2345RootSetEquiv (sigma • alpha) = sigma • s2345RootSetEquiv alpha;
2. arithFrobAt reduction compatibility;
3. factor multiset identification.

## Actual upstream

S2345RootSetEquiv:
  f.rootSet O_L ~= (s2345P f).rootSet L,
  compatible with algebraMap O_L L by rfl.

## Conclusion

- BUILT: S2345 root equivalence.
- MISSING: smul=galRestrict lemma, then root-set action compatibility.
- no fake; no false S2057 data.
