# DEGREE-ONE-GAPS — completionMap self + place equality (A1072)

Status: read-only + partial Lean file; no compile.

## 1. `completionMap = RingHom.id` when Fmod = F (Algebra.self)

`completionMap` (`FinitePlaceExtension:58`):
```lean
def completionMap (place : FinitePlace K) :
    (comap (k := k) place).maximalIdeal.adicCompletion k →+*
      place.maximalIdeal.adicCompletion K
```
Even for `k = K` and `Algebra K K`:
- the domain is the completion at `comap (k := K) place`, not at `place`;
- `comap` is `FinitePlace.mk` of the contraction of the maximal ideal along
  `algebraMap (O K) (O K)`; for `Algebra.id` this contracts to itself, but no
  `comap_self` theorem exists in the tree;
- `completionMap_coe` (`:88`) proves only the dense-field formula
  `completionMap place (x) = algebraMap K K x`;
- to extend to the full completion one needs a density/uniqueness argument
  (`UniformSpace.Completion.ext` / `adicCompletion.ext`) plus `comap_self`.

**Written in `Mzk1CompletionMapSelfActual.lean`:**
- `completionMap_self_coe` (PROVED from `completionMap_coe`);
- `CompletionMapSelfTarget` (explicit Prop):
  `∃ h : comap place = place, HEq (completionMap ...) (RingHom.id ...)`.
- `CompletionMapSelfTargetOfComap` (fixed `h` version).

No full identity is claimed.

## 2. Place equality: `S1487FivePlace` vs `nativeBadLift T b`

- `S1487FivePlace : FinitePlaceAtPrime GaussianField 5`
  (`S1487...:128`) with value
  `concreteGaussianFivePlace = Classical.choose (comap_surjective (k:=ℚ)
  (K:=GaussianField) concreteFivePlace)` (`ConcreteFinitePlaceBoundary:39-49`).
- `nativeBadLift T : NativeBadLift T.arithmetic (nativePlaceSelection T)`
  (`NativeBadLiftActual:22`), with
  `lift b := Classical.choose (comap_surjective (K:=T.arithmetic.F) b.1)`.
- `nativeBadLift_comap` (`NativeReductionFieldsActual:91`) only says
  `comap (nativeBadLift T).lift b = b.1`; it does not compare to
  `concreteGaussianFivePlace`.

With `hT : T.arithmetic = S1487Arithmetic l`, both are places of
`GaussianField`, but they are independent `Classical.choose` outputs from
different `comap_surjective` propositions.  If `b.1` is literally
`concreteFivePlace` and the arithmetic is identified, the propositions become
the same and `Classical.choose` is the same term by definitional reduction;
otherwise the equality is extra source data.

**Written:** `S1487PlaceEqTarget (hT b) : Prop`
```lean
S1487FivePlace.val = hT ▸ ((nativeBadLift T).lift b)
```
and `S1487PlaceEqRoute` note.

## 3. What is needed to close the two gaps

1. `comap_self`
   `comap (k := K) place = place` for `Algebra.id`; likely provable by
   `NumberField.FinitePlace.ext` + `Ideal.comap_id`.
2. `completionMap_id`
   `completionMap (k := K) (K := K) place = ...` after the `comap` cast;
   route: `adicCompletion.ext` + `Completion.ext` using `completionMap_coe`
   and continuity (`continuous_completionMap`).
3. place equality
   either prove `b.1 = concreteFivePlace` for the relevant `b`, or add
   `hplace : S1487FivePlace.val = ...` as explicit source data.

## 4. Verdict

- `completionMap` self identity is **not** definitional; only the dense-field
  formula is proved.
- S1487/native place equality is **not** in the tree; it depends on the chosen
  bad-place selection, not just the arithmetic equality.
- The new file records both as explicit Props; no fake identity/equality.
