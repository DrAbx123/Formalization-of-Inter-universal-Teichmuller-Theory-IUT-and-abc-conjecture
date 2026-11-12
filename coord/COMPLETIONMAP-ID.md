# COMPLETIONMAP-ID — attempt at `completionMap = id` (A1075)

Status: partial Lean attempt; no compile.

## Proof plan

1. `halg : (algebraMap K K : K →+* K) = RingHom.id K`.
2. `comap_self_of_algebraMap_id` (A1073, proved) gives
   `comap (k:=K) place = place`.
3. Rewrite the domain of `completionMap` to `place`.
4. Unfold
   `completionMap = adicCompletion.equiv.symm ∘ mapRingHom (algebraMap) ∘ adicCompletion.equiv`
   (`FinitePlaceExtension:58-69`).
5. With `halg`, `mapRingHom (algebraMap)` is `mapRingHom (RingHom.id)`; the
   completion map of the identity is the identity (`UniformSpace.Completion.map_id`
   or `mapRingHom_id`), and `equiv.symm ∘ equiv = id`.
6. The remaining identity is definitional/simp; if not, use
   `adicCompletion.ext`/`Completion.ext` with `completionMap_coe` on the dense
   image of `K`.

## File

`tmp/sheaf/xif/paper/Mzk1CompletionMapIdActual.lean`:
- `completionMap_id_of_algebraMap_id` (ATTEMPT; last tactic `simp [completionMap, halg]`);
- `CompletionMapIdTarget` (fallback Prop);
- `completionMap_self_coe` (PROVED from `completionMap_coe`).

## If `simp` fails

The first error should identify whether:
- `comap_self` rewrite leaves a type mismatch (expected `HEq`), or
- `mapRingHom`/`adicCompletion.equiv` simp lemmas are missing.
Then replace the final `simp` with:
```lean
apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
apply UniformSpace.Completion.ext
· continuity
· continuity
· intro a; simp [completionMap_coe, halg]
```
or the appropriate `Completion.induction_on` variant.
