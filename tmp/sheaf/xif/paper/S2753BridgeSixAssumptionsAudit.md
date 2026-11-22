# S2753 — bridge six assumptions audit (S2720BridgeActualObjActual)

Date: 2026-11-07. Audit only; no source changes.

## 1. The six assumptions (S2720BridgeActualObjActual)

Carrier: `qVFamTensorBlock T b` with `S2586IQHullLogVolumeInterface`.

## 2. Status table

| assumption | statement | status | evidence / gap |
|---|---|---|---|
| hnull | `S2589SingletonNull (S2586 interface)` | ACTUAL | `S2590SingletonNull` (S2590PadicSingletonNullActual), axioms trio |
| hval | padic valuation bound for ABC support primes | MISSING | only explicit hypothesis; no actual theorem |
| hweightvol | weight ≤ S2586 comparison-region volume | FAIL/INSUFFICIENT | fixed scaleShift=id; S2730HweightvolCounterexampleActual refutes it |
| hunit | unitRegion log ≤ hull log + 0 | MISSING (likely false) | actual S2720BridgeHaarActual gives the OPPOSITE hull ≤ unitRegion; no equality roof |
| hsplit | region ≤ scaled unit + point | ACTUAL | `S2720BridgeHaarActual.normalizedRegion_logVolume_le_split`, trios |
| hptfin | point singleton volume finite | ACTUAL | `S2720BridgeHaarActual.singleton_logVolume_lt_top`, trios |

## 3. Precise remaining gaps on the S2586 carrier

1. hval: no construction of the valuation bound from the actual q-pilot data.
2. hweightvol: cannot be repaired on S2586 because `scaleShift=id` makes the
   region `unitRegion ∪ {point}` measure-zero point; S2730 counterexample.
3. hunit: needs `unitRegion ≤ hull` (with hull = rootNormHull), not implied by
   `hull ⊆ unitRegion`; currently no actual proof.

## 4. S2752 carrier is DIFFERENT — cannot mix

S2752 files use the qPilot line-bundle carrier:

```lean
Ideal (SourceOK (A := S2735Arithmetic l))
S2752J l a b c := supportIdeal (K := (S2735Arithmetic l).K) (abcRationalPoint a c)
S2752_hweightvol : S2736QPilotLineBundleHweightvol (S2752J l) 0
```

whereas S2720 uses the tensor-block carrier

```lean
qVFamTensorBlock T b
S2586IQHullLogVolumeInterface (l := l) T b
```

There is NO transport map between these carriers, nor a region/log-volume
comparison.  In particular:

- S2752 hweightvol is stated over the qPilot fractional ideal/line bundle,
  not over `qVFamTensorBlock T b`;
- it cannot fill S2720 `hweightvol` (different carrier and different log-volume);
- no equality/transport `qVFamTensorBlock → SourceOK/fractional ideal` exists.

## 5. S2752 current status

- `S2752FinalHweightvolActual.lean` source exists (3292 B) but has NO olean.
- First compile errors: invalid field `A` at `SourceOK (A := S2735Arithmetic l)`
  (line 26), unexpected token `⁰` (line 44), unknown `S2752J` (line 30).
- Therefore S2752 is NOT yet actual; its carrier-transport to S2720 is an
  additional bridge gap, not a replacement for hweightvol.

## 6. Conclusion

- Actual: hnull, hsplit, hptfin.
- Missing/false on S2586: hval, hweightvol, hunit.
- S2752 does not close the bridge: different carrier, no transport, not compiled.
- Bridge is not closed; do not claim hweightvol/3.12 closure.
