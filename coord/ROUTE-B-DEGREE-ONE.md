# ROUTE-B-DEGREE-ONE — Fmod = F = K = GaussianField (A1071)

Status: read-only audit + partial file; no compile.

## 1. Does S1487 arithmetic have degree 1?

`S1487Arithmetic l := concreteGaussianInitialThetaArithmeticData l`
(`S1487OQPilotScalarEqualityActual:395`).
`ConcreteFinitePlaceBoundary:25-31` defines:
```lean
def concreteGaussianInitialThetaArithmeticData (l : PrimeGeFive) :
    InitialThetaArithmeticData l where
  Fmod := GaussianField
  F := GaussianField
  K := GaussianField
  tower := gaussianIdentityThetaTower l
  curve := concreteSplitPuncturedCurve.baseChange GaussianField
```
So `Fmod = F = K = GaussianField` definitionally; `Module.finrank Fmod F = 1`
(proved in the new file via `Module.finrank_self`).

## 2. Does `Mzk1ConcreteThetaDataActual` accept this arithmetic?

**No, not directly.**  `Mzk1ConcreteThetaDataActual` is a skeleton for
`Existence.thetaData`, whose inputs are:
- `C : EllipticCurveData` (with its own `F/Fbar/E`),
- `CA : C.CurveArithmetic`,
- `TI : C.TateInputs`,
- `R : C.ModEllRepData ℓ`,
- `hsl`, `hP2`, `hP5`, `hcore`, and `7 ≤ ℓ`.

Gaussian arithmetic alone supplies `InitialThetaArithmeticData`, not an
`EllipticCurveData`/Tate/modular-representation package.  The skeleton's
hypotheses could be *supplied* if such C/CA/TI/R existed over `GaussianField`,
but none is constructed.  Also `thetaData` requires `ℓ ≥ 7`, whereas S1487 is
used at `ℓ = 5` (though S1487Arithmetic is parameterized by l).

## 3. Degree-one specialization of Route B

With `hI : I.initial.arithmetic = S1487Arithmetic l` and
`hT : T.arithmetic = S1487Arithmetic l`, all three fields become
`GaussianField`; `completionMap` for `Fmod=F` is the completion of the
identity algebra, and `carrier_eq` becomes a type equality of completions of
places of the same field.

However, even then:
- the C3 place `C3LogShellPlaceL C3L i` and the native qVFam place
  `qVFamTensorPlace T (toBad i)` are **different arbitrary places** of
  `GaussianField`; no equality is in the tree;
- `completionMap` for the identity algebra is not definitionally `RingHom.id`;
  a theorem `completionMap_id` / `comap_eq` is missing;
- `p_compat` (`C3L.p = qVFamTensorP`) must follow from the place equality, but
  no theorem states it.

## 4. Written file

`tmp/sheaf/xif/paper/Mzk1RouteBBridgeDegreeOneActual.lean`:
- `S1487Arithmetic_Fmod_eq_F`, `_F_eq_K` (`rfl`);
- `S1487Arithmetic_finrank_one` (`Module.finrank_self`);
- `DegreeOneBaseChangeData` with:
  - `hI`, `hT` arithmetic equalities;
  - `toBad`;
  - `place_eq`, `p_compat`, `comap_eq` as explicit `Prop` fields;
- `DegreeOneBaseChangeObstruction : Prop`;
- `DegreeOneIdentityTarget : Prop` (identity of the transported
  `baseChangeRingHomL`; not proved).

## 5. What would make degree-one a real `RingEquiv`

1. **Place equality**
   `C3LogShellPlaceL C3L i = comap (qVFamTensorPlace T (toBad i))`
   (after `hI/hT`, both are places of `GaussianField`).
2. **`comap` identity**
   `comap (k := GaussianField) (place) = place` for the identity algebra.
3. **`completionMap` identity**
   `completionMap (place) = RingHom.id` for the identity algebra; or at least
   a ring equivalence between the two completions.
4. **p compatibility** from the place equality.

With these, `BaseChangeMapL.carrier_eq` becomes a type equality of completions
of the same place, and `baseChangeRingHomL` is the identity; a `RingEquiv` can
then be assembled from `RingHom.id`/`RingEquiv.refl`.  None of (1)-(4) is
currently in the tree.

## 6. Verdict

- S1487 arithmetic is exactly degree one (`Fmod=F=K=GaussianField`).
- `Mzk1ConcreteThetaDataActual` cannot consume it directly (needs
  curve/Tate/modular data, and ℓ≥7).
- Degree-one removes the **field-extension** obstruction but not the
  **place** obstruction; the identity/`RingEquiv` target is an explicit Prop
  in the new file, not proved.
- The remaining missing declarations are exactly `place_eq`, `comap_eq`,
  `completionMap_id`, `p_compat`.
