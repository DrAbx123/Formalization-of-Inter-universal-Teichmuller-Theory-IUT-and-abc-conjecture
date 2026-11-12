# GAP-LINEAR-HULL — q-linear terms in `gap` (A1076)

Status: source-level algebra; no compile.  `A := qPilot.absLogQ = logQ/(2ℓ)`,
`qOrder = v(q)`; `Q := logQ = qOrder·logp` weighted.

## 1. Definitions

- `gap := rhs - logVol(lgp·hull(vcI))` (`Gap.lean:505`).
- `gap_eq_rhs_add` (`:523`):
  `gap = rhs + sFactor(nC)·A - logVol(hull(vcI))`.
- `gap_eq` (`:961`):
  `gap = (1/nC) Σ_i Σᶠ_vQ gapHullAt i vQ`.
- `gapHullAt` (`:895`): finite `p` = `Σ_c w_c · ind2Term`; `∞` = 0.
- `ind2Term` (`:747`):
  `componentVol(leastHull(thetaComponent))
    - componentVol(scaleElt • leastHull(shell))`,
  `ind2Term ≥ 0` (`:756`).
- `gapTerm` (`:639`) = `vol(leastHull(thetaComponent)) - vol(lgpComp)`.

Scaling: `scaleElt = qroot^{j²}` (`ThetaRegion:126-136`);
`ord_p(qroot) = qOrder/(2ℓ·e)` (`Data:327-330`); hence the q-scaling term
in `componentVol(scaleElt • ...)` is `-j²·qOrder·logp/(2ℓ)` per factor.

## 2. q-linear candidates

### (a) `componentVol(scaleElt • leastHull(shell))`
`componentVol` is additive under unit scaling:
`μ(a•X) = μ(a•O) + μ(X)` (`IdentifiedCopies:67`);
for `a = qroot^{j²}`, `μ(a•O) = -j²·qOrder·logp/(2ℓ)`.
With the `(1/nC)Σ_iΣ_c w_c Σ_j` aggregation this is `-sFactor(nC)·A`.
**Sign: negative**, coefficient `-sFactor` in A-units.

### (b) `rhs` (theta-pilot hull log-volume)
The theta component is `⋃_{indAut} scaleElt • shell`;
`leastHull` of the union.  In the iv reading the `indAut` union is a
bounded enlargement (`ind2Term`), and the scaling law gives
`rhs = -sFactor(nC)·A + bounded`
(the `-sFactor·A` piece is the scaling of the shell hull).
**Sign: negative linear plus bounded.**

### (c) `logVol(hull(vcI))`
`vcI` is the unscaled tensor log-shell (`Ind3:58/80/123`);
its volume is **q-independent** (no `scaleElt`),
`V = logVol(hull(vcI))`.
**Sign: no q-linear term.**

### (d) `gap` from (a)-(c)
`gap = rhs + sFactor·A - V`
     `= (-sFactor·A + bounded) + sFactor·A - V`
     `= bounded - V`.
So the explicit `+sFactor·A` cancels the `-sFactor·A` from `rhs`;
**no `+c·A` term remains** in `gap` at this algebraic level.

### (e) `ind2Term` leading term
`ind2Term` measures the enlargement of `leastHull(⋃ indAut images)` over
`scaleElt • leastHull(shell)`.  Since `scaleElt` is a unit and scaling commutes
with `leastHull` (`leastHull_units_smul`), the q-scaling factor appears on both
terms and cancels; `ind2Term` is a **bounded** enlargement (iv reading).
Paper/lana derivation: `ind2Term = frac(j²·v_p(q)/(2ℓ))·logp`
(`coord/C0-EXACT-DERIVATION`, lana marks it Open);
as a `frac`, it is bounded in `[0,logp)` per component and **not ∝ A**.

### (f) `orderVol` / `shellExcess` / `logShellRadius`
- `orderVol` (`VcI:93`) is q-independent; bounded by
  `-Σ differentExponent·logp` (`VcI:109-113`);
- `shellExcess` (`VcI:158`) is q-independent; tame `Σ(1-1/e)logp` (`:414`);
- `logShellRadius` (`VcI:464`) is a shell-geometric `sSup(-ordp)`, q-independent.
None contributes `c·A`.

## 3. Is there a `+c·A` term (c>0)?

**No** in the `gap` expansion at the algebraic level:
- the only q-linear piece is `-sFactor·A` from the theta scaling and the
  corresponding `-sFactor·A` inside `rhs`;
- `gap = rhs + sFactor·A - V` cancels it;
- `ind2Term`, `orderVol`, `shellExcess`, `logShellRadius`, archDefect are
  bounded/q-independent;
- `V` is q-independent.

Thus `gap` has no positive q-linear term; its q-dependence is at most bounded
(via `ind2Term`'s `frac`), consistent with
`coord/DECOMP-ROUND2.md` (no ∝m positive term in lana sources).

## 4. Comparison with paper constants

- `sFactor(nC)·A = (l(l+1)/12)·(Q/(2l)) = (l+1)/24 · Q`.
  This is exactly the `(l+1)/24` coefficient in IUT IV, Theorem 1.10 proof
  Step (v) after the `j`-average (`− (l+1)/24·log(q_{vQ})`).  The `gap`
  cancellation leaves no residual `(l+1)/24·Q` in `gap`; it is the coefficient
  of the rhs scaling before cancellation.
- `1/6` appears in the final Theorem 1.10 bound
  (`1/6·log(q) ≤ ...`) and in the `CTheta` bracket
  `−(1/6)(1−12/l²)·log(q)` (S2691 `cThetaBracket`), not as a q-linear
  coefficient of `gap`.
- The paper's `CTheta` formula has the q-linear term inside the bracket;
  `gap` is a different object (hull vs LGP-hull difference), so `1/6` does not
  appear as a gap coefficient.

## 5. Lean anchors

| item | source |
|---|---|
| `gap` | `Iut/WallEquiv/Gap.lean:505` |
| `gap_eq_rhs_add` | `Gap.lean:523` |
| `gap_eq` | `Gap.lean:961` |
| `gapHullAt` | `Gap.lean:895` |
| `ind2Term`, `ind2Term_nonneg` | `Gap.lean:747/756` |
| `gapTerm` | `Gap.lean:639` |
| `scaleElt/scaleEltAt` | `Iut/Concrete/ThetaRegion.lean:126/136` |
| `ordp_qrootOf` | `Iut/Concrete/ThetaLocalConstruct/Data.lean:327` |
| `componentVol_units_smul` | `Iut/Wall/IdentifiedCopies.lean:67` |
| `orderVol/shellExcess` | `Iut/WallEquiv/VcI.lean:93/158` |
| `logShellRadius` | `Iut/WallEquiv/VcI.lean:464` |
| `vcI/vcIComp` | `Iut/Wall/Ind3.lean:58/123` |

## 6. Caveat

This is an algebraic reading of the definitions; the exact `ind2Term` `frac`
formula is marked Open in lana and derived in `coord/C0-EXACT-DERIVATION`.
No numerical evaluation of `gap` is claimed here.
