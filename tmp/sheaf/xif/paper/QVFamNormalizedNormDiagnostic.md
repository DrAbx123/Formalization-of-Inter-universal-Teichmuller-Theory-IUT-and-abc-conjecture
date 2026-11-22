# qVFamily normalized/default norm diagnostic

Date: 2026-10-29. Status: diagnostic only; not a target condition.

## Decision

Normalized spectral norm and default completion valuation norm are **not**
unified for the final target. The exact ratio formula below is retained as a
diagnostic record. No final target, comparator, or axiom audit may require
`QVFamNormInstanceGap`, `QVFamNormalizedCoefficientGap`, or any equality of
the two norm instances.

## Retained exact formula

For the actual qVFamily q:

```text
c_norm * log p
  = (qVFamily T b).order * log(residueNormBase (qVFamTensorPlace T b))
      - log( ||q||_normalized / ||q||_default )
```

where

```text
c_norm = -logb_p ||q||_normalized
qVFamNormRatio = ||q||_normalized / ||q||_default
```

The formula is proved in
`tmp/sheaf/xif/paper/QVFamNormalizedCoefficientBridgeActual.lean` (EXIT 0).

## Exactly what is not claimed

- No equality `||q||_normalized = ||q||_default`.
- No equality `c_norm = qVFamilyLatticeCoefficient`.
- No equality of `QVFamNormalizedCoefficient` with the default-norm coefficient.

## Consumers

`QVFamNormInstanceGap` and `QVFamNormalizedCoefficientGap` have no consumers
outside the diagnostic files. Final Target list / axiom audit do not include
them.
