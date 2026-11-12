# PLACE-EQ-SPECIALIZATION — comap_self / completionMap_id / S1487 place (A1073)

Status: read-only + partial Lean file; no compile.

## 1. `comap_self`

`comap` (`FinitePlaces:61-76`) is
`FinitePlace.mk` of
`place.maximalIdeal.asIdeal.comap (algebraMap (O K) (O K))`.

An arbitrary `Algebra K K` need not have `algebraMap K K = RingHom.id K`.
Therefore `comap (k:=K) place = place` requires the explicit hypothesis
```lean
halg : (algebraMap K K : K →+* K) = RingHom.id K.
```
With it, the proof is:
- `rw [← FinitePlace.mk_maximalIdeal place]`;
- `FinitePlace.mk_eq_iff` reduces to equality of height-one spectra;
- `HeightOneSpectrum.ext` reduces to equality of `asIdeal`;
- `comap_maximalIdeal`, `halg`, `Ideal.comap_id` close it.

`Mzk1PlaceEqSpecializationActual.comap_self_of_algebraMap_id` implements this.
(For the concrete Gaussian arithmetic, `algebraFmodF` is synthesized as
`Algebra.id`, so `halg` is expected to be `rfl` there; this is not assumed
globally.)

## 2. `completionMap_id`

After `comap_self`, domain and codomain of
`completionMap (k:=K) (K:=K) place` are completions of the same place.
The dense formula is green:
`completionMap_coe` (`FinitePlaceExtension:88`) gives
`completionMap place (x) = algebraMap K K x`; with `halg`, this is `x` on the
dense image of `K`.

Extending from the dense image to the full adic completion requires:
- `adicCompletion.ext`/`Completion.ext`;
- continuity of `completionMap` (`continuous_completionMap`, `:72`) and of the
  identity;
- `UniformSpace.Completion.ext` applied to the underlying completion.

The new file records the target:
```lean
def CompletionMapIdTarget (halg place) : Prop :=
  HEq (completionMap (k:=K) (K:=K) place)
    (RingHom.id (place.maximalIdeal.adicCompletion K))
```
not proved.  No fake identity is asserted.

## 3. S1487 / native place specialization

- `S1487FivePlace = ⟨concreteGaussianFivePlace, proof⟩`
  (`S1487...:128`); `concreteGaussianFivePlace` is
  `Classical.choose (comap_surjective (k:=ℚ) (K:=GaussianField) concreteFivePlace)`.
- `nativeBadLift T` (`NativeBadLiftActual:22`) chooses
  `Classical.choose (comap_surjective (K:=T.arithmetic.F) b.1)` for
  `b : Bad (nativePlaceSelection T)`.
- `nativeBadLift_comap` (`NativeReductionFieldsActual:91`) only gives
  `comap (nativeBadLift T).lift b = b.1`.

To obtain the place equality as `rfl`/proof, one needs a **data choice**:
a native bad place `b` whose underlying Fmod place is exactly
`concreteGaussianFivePlace`, plus the arithmetic identification
`T.arithmetic = S1487Arithmetic l`.  This is recorded as
```lean
def S1487NativeFivePlaceExists (hT) : Prop :=
  ∃ b : Bad (nativePlaceSelection T),
    b.1 = hT.symm ▸ concreteGaussianFivePlace
```
and the place equality target
```lean
def S1487PlaceEqTarget (hT b) : Prop :=
  S1487FivePlace.val = hT ▸ ((nativeBadLift T).lift b).
```

Without that data choice, the equality is not derivable: the bad-place
selection `nativePlaceSelection T` is an arbitrary source set; there is no
proof that it contains the concrete Gaussian five place.

## 4. Verdict

- `comap_self` is **proved** under the explicit `halg`.
- `completionMap_id` is reduced to the dense-extension problem; target recorded,
  not proved.
- S1487 place equality is **not** automatic; it requires a data-specialized
  native bad place `b` with `b.1 = concreteFivePlace`, plus arithmetic equality.
- No fake equality/identity; all remaining assumptions are explicit Props.
