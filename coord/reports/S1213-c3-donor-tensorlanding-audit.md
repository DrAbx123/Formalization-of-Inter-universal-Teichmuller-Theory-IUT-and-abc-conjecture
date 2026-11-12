# S1213: C3 donor roots / kummerClass / rootChange / tensorLanding audit

Date: 2026-10-30. Report only, no new Lean.

Files read: ConcreteC3DonorActual, ConcreteC3DonorCompletionActual,
ConcreteC3RootTensorActual, ConcreteC3DonorAssemblyActual,
BaseTensorInsertionActual, ActualC3DonorFromNative, ConcreteC3RootCompletionActual.

## 1. Actual fields

`ConcreteC3DonorActual`:

- actual p, finite place `place`, q candidate `concreteQCandidate`;
- actual q unit `concreteQUnit : (CommonPrimeCompletion (K := Fmod) place)ˣ`;
- actual theta packet `(I.theaterAt 0 0).thetaPacket`.

`ConcreteC3RootTensorActual`:

- actual algebraic closure `ConcreteQAlgebraicClosure`;
- actual q unit in the algebraic closure `concreteQUnitAlgebraicClosure`;
- actual root systems `concreteRootsAlgebraicClosure`,
  `concreteRootsPrimeAlgebraicClosure : NatRootSystem concreteQUnitAlgebraicClosure`;
- actual power law `concreteRootsAlgebraicClosure_pow`.

`ConcreteC3DonorAssemblyActual`:

- actual `rootsAlgClosure`, `rootsPrimeAlgClosure`;
- actual `rootChangeAlgClosure := KummerClass.rootSystemDiff rootsAlgClosure rootsPrimeAlgClosure`;
- actual concrete tensor index/places/tuple/tensorUnit = 1.

`BaseTensorInsertionActual` (native X, PUnit index) is actual:

- `baseTensorInsertion z := ⨂ z`;
- `baseTensorInsertion_ne_zero`;
- `baseTensorDataActual.tensorLanding := baseTensorInsertion`;
- `tensorLanding_q : baseTensorInsertion q = tensorUnit`, where
  `tensorUnit := Units.mk0 (baseTensorInsertion q) ...`.

## 2. Exact first fields still missing

### roots / roots'

The concrete donor has actual **algebraic-closure** root systems, but
`SourcePilotRegionDonors` requires roots in the completion:

```lean
roots  : NatRootSystem A.qUnit
roots' : NatRootSystem A.qUnit
A.qUnit : (CommonPrimeCompletion (K := Fmod) place)ˣ
```

`ConcreteC3DonorMissingFields.roots/roots'` are exact.

`ConcreteC3RootTensorActual.ConcreteCompletionRootObstruction` records
`Nonempty (NatRootSystem concreteC3QUnit)`.  The completion is not
algebraically closed; actual roots live in `ConcreteQAlgebraicClosure`.

### kummerClass

Exact:

```lean
kummerClass : CyclotomicTower (CommonPrimeCompletion (K := Fmod) place)
```

`ConcreteC3DonorActual.ConcreteKummerClassCarrier` is only the carrier type;
no actual `CyclotomicTower` element over the completion is constructed.

### rootChange

Exact for the completion:

```lean
rootChange : CyclotomicTower (CommonPrimeCompletion (K := Fmod) place)
rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots'
```

Actual only in the algebraic closure:

```lean
rootChangeAlgClosure : CyclotomicTower (AlgebraicClosure completion)
```

## 3. tensorLanding

`ConcreteTensorLandingTarget` fixes

```lean
landing : CommonPrimeCompletion → ConcreteTensorBlock
landing q = concreteTensorUnit   -- and concreteTensorUnit = 1
```

`ConcreteTensorLandingData` / `ConcreteC3DonorMissingFields.tensorLanding`
similarly require `tensorLanding q = A.tensorUnit`, where the actual assembly
uses `concreteTensorUnit = 1`.

The concrete source supplies no completion-to-tensor landing map.  The
existing actual donor `baseTensorInsertion` is over the native X/PUnit
factor, not the concrete `FinitePrimePlace 2 7` tensor block, and it lands at
`baseTensorInsertion q` (nonzero), not at 1: it sets the tensor unit to that
same insertion value.

## 4. Can a landing block be built from q_v/tensor data?

Yes, in the **insertion** sense, with a changed tensorUnit:

```lean
concreteInsertion : CommonPrimeCompletion place → ConcreteTensorBlock
concreteInsertion z := ⨂_{i : FinitePrimePlace 2 7} z
tensorUnitInsertion := Units.mk0 (concreteInsertion q) (nonzero)
tensorLanding_q := rfl
```

This is the direct analogue of `baseTensorInsertion`, but over the concrete
finite tensor index.  It would give an actual `ConcreteTensorLandingData`
provided the diagonal nonzero lemma:

```lean
theorem finitePadicTensorTprod_diagonal_ne_zero
    {M} [NormedAddCommGroup M] [NormedSpace ℚ_[p] M]
    (z : M) (hz : z ≠ 0) :
    finitePadicTensorTprod (p := p) (fun _ : ι => M) (fun _ => z) ≠ 0
```

for finite `ι = FinitePrimePlace 2 7`.  The existing
`BaseTensorInsertionActual.finitePadicTensorTprod_single_ne_zero` proves only
the PUnit one-factor case by coordinates; the finite-index diagonal version is
the exact missing sublemma.

With the diagonal lemma, the tensor block/unit/landing can be made actual, but
the resulting tensorUnit is `concreteInsertion q`, not the fixed
`concreteTensorUnit = 1`.  Therefore:

- `ConcreteTensorLandingData` with arbitrary tensorUnit: constructible from
  insertion + diagonal nonzero lemma;
- `ConcreteTensorLandingTarget` with tensorUnit = 1: not constructible from
  this donor; its q-law would require `concreteInsertion q = 1`.

Any map `q ↦ 1` could be produced by arbitrary `Classical.choice`/if-then,
but has no source provenance and is exactly the fake landing the existing file
refuses.

## 5. Exact conclusion

- actual: p/place/q/qUnit/theta; algebraic-closure roots/roots'/rootChange;
  concrete tensor index/places/tuple/unit=1; native baseTensorInsertion and
  BaseTensorData over X.
- exact first fields for the concrete donor:
  1. `roots, roots' : NatRootSystem qUnit` in the completion;
  2. `kummerClass : CyclotomicTower (CommonPrimeCompletion ...)`;
  3. `rootChange : CyclotomicTower (CommonPrimeCompletion ...)` with
     `rootSystemDiff` law;
  4. `tensorLanding` with fixed unit 1 (or changed unit plus diagonal nonzero
     lemma).
- the q_v/tensor donor supplies an insertion landing only if the tensor unit
  is allowed to be `concreteInsertion q`; fixed `1` remains exact.
- No new Lean written; EXIT=0 report.
