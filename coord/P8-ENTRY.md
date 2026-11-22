# P8 mathematical entry (rewritten 2026-11-16)

Status: route note, statement-stage only; **not compiled/verified** in Lean.

## What changed

- **Dropped**: `belyiAllCompactSequence_uniformEpsilon` (and the
  `belyiAllCompactSequence` family `x ↦ x²/(n+2)`) is **removed as a P8
  premise**.  It is only a concrete polynomial sequence on compact subsets
  of ℚ (a restricted-K toy uniform-epsilon witness), not an actual P8
  arithmetic input.
- **New P8 entry**: arithmetic height estimate on the actual Fermat scheme,
  stated through the canonical line bundle and the arithmetic conductor /
  discriminant data.  This replaces the previous `P8UniformHeightBound`
  phrasing at the route level (the old consumer files remain as conditional
  wrappers).

## New entry (paper-level statement)

### Objects

- `n ≥ 3` (or the admissible range used by the route),
- `Y_n`: the actual Fermat scheme
  `Proj ℚ[X,Y,Z] / (X^n + Y^n - Z^n)` (smooth proper curve over ℚ;
  construction requires the graded quotient + closed subscheme, see below),
- `ω_{Y_n}`: canonical line bundle on `Y_n`,
- `K_y`: a number field, `y : Y_n(K_y)` an actual point (e.g. the point
  attached to a primitive abc triple via the Fermat/Frey construction),
- `h_{ω_Y}(y)`: the local/arithmetic height of `y` with respect to `ω_{Y_n}`
  (normalized arithmetic degree of `y^* ω_{Y_n}` divided by `[K_y : ℚ]`),
- `log diff(k(y)/ℚ)`: `log |Disc_{K_y/ℚ}|` (logarithmic discriminant of the
  residue field extension),
- `N(y)`: the arithmetic conductor attached to `y` (Frey/Fermat conductor
  data of the associated elliptic curve / cover; actual construction needed).

### G1b (uniform height estimate)

For every `ε > 0` there exists `C_ε` such that for all `n` in the admissible
range and all actual points `y : Y_n(K_y)` in the route's family,

```
h_{ω_Y}(y) ≤ (1 + ε) * ( log diff(k(y)/ℚ) + log N(y) ) + C_ε .
```

(This is the G1b line-bundle height estimate; `C_ε` depends only on `ε`,
not on `n` or `y`.)

### P8 target

From G1b plus the Fermat/Frey comparison (`h_{ω_Y}(y)` vs the abc height
`log c` and the radical/weight term) derive the ABC height bound
`log c ≤ (1+ε) * arithmeticWeight(x) + C'_ε`; composing with the accepted
`abcConjecture_iff_abcArithmeticWeightHeightBound` gives ABC.

## Concrete construction of Y_n (Mathlib API; no graded quotient needed)

Mathlib already provides the projective spectrum and ideal-sheaf API; the
Fermat scheme is constructed directly:

1. `fermatPolynomial n := X 0 ^ n + X 1 ^ n - X 2 ^ n` in
   `MvPolynomial (Fin 3) ℚ` (a homogeneous polynomial of degree `n`),
2. the projective zero locus
   `ProjectiveSpectrum.zeroLocus 𝒜 {fermatPolynomial n}` (Topology.lean),
3. the ideal sheaf `Scheme.IdealSheafData.vanishingIdeal` of that closed set
   (IdealSheaf/Basic.lean:565),
4. `Scheme.IdealSheafData.subscheme` (IdealSheaf/Subscheme.lean:448) gives
   the actual Fermat scheme `Y_n` as a closed subscheme of
   `ProjectiveSpectrum`; closed immersion and properness are available from
   the Mathlib API (`ProjectiveSpectrum/Proper.lean`).

## Remaining real objects (no full AG blocker)

1. scheme-level canonical line bundle `ω_{Y_n}` (and `y^*ω_{Y_n}`),
2. the actual point `y : Y_n(K_y)` over the number field `K_y`,
3. the local height `h_{ω_Y}(y)` (arithmetic degree of `y^*ω` divided by
   `[K_y : ℚ]`),
4. `log diff(k(y)/ℚ)` and the arithmetic conductor `N(y)`,
5. the G1b estimate itself (the open arithmetic content, expected
   ABC-level).

## Audit consequences

- All prior P8 entries that used `belyiAllCompactSequence_uniformEpsilon` as
  a premise are **not** route-valid P8 inputs; keep them only as restricted-K
  toy records / conditional wrappers.
- G1b replaces `P8UniformHeightBound` as the P8 mathematical target at the
  route level; `P8UniformHeightBound`/`FreyHeightBound` consumers remain
  conditional wrappers, not the new entry.
- No compile in this correction; Lean statement files for the new entry are
  the next step.


## Mainline shortcuts (recorded 2026-11-16)

### (1) G1a: two affine charts + monic degree n^2 map to P1 + explicit canonical differential

No general Riemann–Hurwitz / scheme-level canonical-bundle theory is needed:

- cover `Y_n` by the two affine charts
  `Z ≠ 0: x^n + y^n = 1` and `X ≠ 0` (or `Y ≠ 0`), glued on the overlap;
- construct the monic map to `P1` of degree `n^2` given by a degree-`n^2`
  coordinate projection (e.g. `[X:Y:Z] ↦ [X^n : Z^n]`) and check it is monic
  and finite on both charts;
- write the canonical differential explicitly on the charts (e.g.
  `ω = dx / y^(n-1)`, up to a unit) and glue it on the overlap; this gives the
  scheme-level `ω_{Y_n}` without general RH.

So the remaining G1a objects are the chart/map/differential check and the G1b
height estimate, not a general AG Riemann–Hurwitz development.

### (2) P6: M = Q/(2l) sandwich → hCor312, without S2953 coefficient equality

- set `M := Q/(2l)` (with `l`, `Q` the IV parameters);
- P5 gives the lower side `-M ≤ H_theta` (from the actual P5
  `qPilotRealifiedLogVolume ≤ qVFamThetaReading`, rewritten in the paper
  normalization);
- P6 gives the upper side `H_theta ≤ U` (the Box(11)/Thm 1.10 paper bound);
- the two-sided sandwich `-M ≤ H_theta ≤ U` yields `hCor312`
  (`thm110Lhs T ≤ thm110Mid T + thm110Cor312Gap T`) directly;
- the S2953/CTheta coefficient equality (`CThetaPaper = B/qAbs`) is **not a
  premise** of this route.

Hence `hCor312` becomes a P5/P6 sandwich consequence; the S2953
`S2953CThetaUpperCertificate` remains an auxiliary interface, not an input.
