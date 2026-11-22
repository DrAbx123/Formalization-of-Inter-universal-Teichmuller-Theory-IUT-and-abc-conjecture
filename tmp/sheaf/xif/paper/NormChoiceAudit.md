# qVFamily norm choice audit (corrected)

Date: 2026-10-29

## Question

Does the paper q_v live in the default completion valuation norm, or in the
CommonPrimeCompletion normalized spectral norm used by the tensor fractional
lattice construction?

## Correction

A default-norm tensor block is **not constructible** in the current tree:
there is no compatible `NormedSpace Q_p` instance for the tensor block over
the default completion norm.  The normalized spectral norm of
`CommonPrimeCompletion` / `NormalizedCompletion` is therefore the **only actual
tensor norm** available for the fractional-lattice/measure construction.

Consequently the final proof uses the normalized coefficient `c_norm`, not the
default `localLogMagnitude`:

```text
qPilot region       = F(c_norm) * O_hol
root theta region   = F(j^2 * (c_norm/(2l))) * O_hol
```

This is a tensor-normalization choice forced by the existing actual tensor
carrier, not an identification `c_norm = default local log`.

## Actual data

- `QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedGenerator` gives the
  actual normalized generator and its norm identity.
- `qVFamNormalizedPureFractionalScalingData` is the actual scaling data at
  `c_norm`.
- `qVFamNormalizedCoefficient_pos` / `qVFamNormalizedCoefficient_nonneg` prove
  the coefficient is positive.
- `RootNormalizedContainmentActual.rootHalfCoefficient = c_norm/(2l)` and proves
  `rootHalfCoefficient <= rootNormCoefficient`.
- `RootHullContainmentInequalityActual` gives
  `qPilotNormRegion subset rootNormHull` and the local inequality via
  normalized-log monotonicity.

## Decision

**Normalized spectral norm is the only actual tensor norm.**  The paper q-pilot
scalar in the final tensor proof is `c_norm`; the default-norm
`localLogMagnitude (qVFamily)` is not used as the tensor scalar.

## Not claimed

- No default-norm tensor block: it is unavailable.
- No equality `c_norm = localLogMagnitude(qVFamily)`.
- No norm-instance equality.
- No root hull equality; only containment/monotonicity.

## Remaining actual facts for the final proof

The normalized containment file still requires the actual Haar facts

```text
0 < mu (qPilotNormRegion)
mu (rootNormHull) < top
```

These follow from the actual fractional-lattice scaling data and compact
canonical unit reference once the pure-generator/unit-tensor action is
transported to `mu`; that transport is the remaining measure step.
