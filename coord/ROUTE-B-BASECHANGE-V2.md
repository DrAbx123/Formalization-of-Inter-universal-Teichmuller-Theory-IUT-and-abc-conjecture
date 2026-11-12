# ROUTE-B-BASECHANGE-V2 — base-change map, not ring equivalence (A1070)

Status: design + file `Mzk1RouteBBridgeActual.lean` rewritten; no compile.

## 1. Direction correction

`Fmod ⊆ F` is recorded in `InitialThetaArithmeticData`
(`LeanFormal/IUT/IUTI/InitialTheta/ArithmeticData.lean:62-81`):
fields `[algebraFmodF : Algebra Fmod F]`, `[finiteFmodF]`, `[galoisFmodF]`.
Thus there is no ring equivalence `Fmod-completion ≃+* F-completion` in general;
the canonical map is the **algebra extension**
`NormalizedCompletion (Fmod place) →+* NormalizedCompletion (F place)`.

The actual construction is
`NumberFieldFinitePlace.completionMap` (`Foundations/NumberField/FinitePlaceExtension.lean:58`):
```lean
def completionMap (place : FinitePlace K) :
    (comap (k := k) place).maximalIdeal.adicCompletion k →+*
      place.maximalIdeal.adicCompletion K
```
for `Algebra k K` and an upstairs place `place` of `K`; it is a ring hom,
uniformly continuous (`continuous_completionMap`, `:72`), **not** an equivalence.
Here `k = T.arithmetic.Fmod`, `K = T.arithmetic.F`, and the upstairs place is
`qVFamTensorPlace T b`.

## 2. `BaseChangeMapL` (new file)

`Mzk1RouteBBridgeActual.lean`:
```lean
structure BaseChangeMapL where
  toBad : C3L.tensorIndex → Bad (nativePlaceSelection T)
  carrier_eq : ∀ i,
    CommonPrimeCompletion (C3LogShellPlaceL i) =
      NormalizedCompletion (comap (k := T.arithmetic.Fmod) (qVFamTensorPlace T (toBad i)))
  p_compat : ∀ i, C3L.p = qVFamTensorP T (toBad i)
```
The map itself is constructed by transporting `completionMap` along
`carrier_eq`:
```lean
noncomputable def baseChangeRingHomL (B) (i) :
    CommonPrimeCompletion (C3LogShellPlaceL i) →+*
      NormalizedCompletion (qVFamTensorPlace T (B.toBad i)) :=
  Eq.ndrec (motive := fun X => X →+* NormalizedCompletion (...))
    (completionMap (k := T.arithmetic.Fmod) (K := T.arithmetic.F)
      (qVFamTensorPlace T (B.toBad i)))
    (B.carrier_eq i)
```
This is a genuine **Fmod-completion → F-completion** map; no `≃+*` is introduced.

## 3. Place map

`BadToC3TensorMapL` has `toBad : C3L.tensorIndex → Bad (...)` plus
`basePlace_compat`/`thetaValue_compat` Props.  `badToC3TensorMapLOfEquiv` builds
it from an explicit index equivalence.  `BadToC3TensorMapLObstruction` records
the exact missing data.

## 4. p compatibility

`p_compat : C3L.p = qVFamTensorP T (toBad i)` is an explicit field.
It follows from the carrier/place equality in principle (the residue
characteristic of `comap (qVFamTensorPlace)` is `qVFamTensorP`), but no theorem
in the tree states it.  Keeping it explicit avoids a hidden cast.

## 5. Base-changed block (not in this file yet)

For a `B : BaseChangeMapL`, Route B defines
```lean
abbrev RootFiber (i) := NormalizedCompletion (qVFamTensorPlace T (B.toBad i))
abbrev C3RootBlock := FinitePadicTensor (fun i => RootFiber i)
```
The **base-change map** is used as a `ℚ_[p]`-algebra/linear map
`C3LogShellTensorBlockL → C3RootBlock` (componentwise `baseChangeRingHomL`),
not as an equivalence.  The qroot unit `rootNormedUnit T (B.toBad i)` lives in
`rootNormedExtension` over `RootFiber i`; its tensor is an element of the
base-changed block, so multiplication by it is defined there.

## 6. Haar scaling path

On `C3RootBlock` (finite product of finite extensions of `ℚ_[p]`):
- `Measure.addHaar` is available;
- multiplication by a unit `u` scales Haar by the distributive Haar character
  `distribHaarChar u` (Mathlib), or by `‖u‖` in the local-field normalization;
- existing pieces: `FinitePadicHaarScaling.measure_prime_smul_finiteDimensional`
  (`:25`), `log_measure_prime_smul_finiteDimensional` (`:54`), and
  `arithmeticTupleNormalizedLogVolume_primeScalar_zpow` (`:510`).
A general unit scaling lemma must be proved for `C3RootBlock` (port batch L
for the general `distribHaarChar` law; no TG dependency).

## 7. Verdict

- The correct Route B map is `completionMap` (Fmod-completion → F-completion),
  not a ring equivalence.
- `Mzk1RouteBBridgeActual.lean` now records the base-change data and constructs
  the transported `baseChangeRingHomL` from an explicit `carrier_eq`.
- The remaining exact GAPs are:
  1. `I.initial.arithmetic.Fmod` vs `T.arithmetic.Fmod` identification;
  2. `C3LogShellPlaceL i` = `comap (qVFamTensorPlace T b)` place equality;
  3. `p_compat`;
  4. base-changed tensor block + Haar scaling (next file).
- No fake equiv, no `RingEquiv.refl` on unequal fields.
