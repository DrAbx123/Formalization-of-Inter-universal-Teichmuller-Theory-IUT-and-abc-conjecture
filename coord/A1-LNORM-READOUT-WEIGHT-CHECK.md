# New LNormReadout fix vs A1 weight convention — read-only check

Date: 2026-11-14. Lane: stage4. **Read-only note; no Lean file was modified or added.**

## Files inspected

- `tmp/sheaf/xif/paper/Mzk1P0LNormReadoutActual.lean` (rewritten 09:19 local)
- `tmp/sheaf/xif/paper/Mzk1P0LNormReadoutProductActual.lean` (rewritten 09:19 local)
- A1 side: `Mzk1A1DeltaExplicitActual`, `Mzk1A1QhatSaturationReadoutActual`, `Mzk1A1SignedReadoutProductActual`
- Reference for the old weight convention: `ProcessionNormalizationWeightsActual.localCompletionDegree/nativeBadLocalWeight`

## Weight conventions found

### LNormReadoutProductActual
`thetaNormReadProduct = log(hullMass) - log(unitMass)` and
`thetaNormReadProduct_eq_sum : thetaNormReadProduct = sum_b (s1915LocalDegree T b) * log r_b`,
`thetaNormReadProduct_eq_closedForm_sub_one : ... = s1915ClosedForm T - 1`.
**Weights are `s1915LocalDegree`** — exactly the A1/product weights.

### LNormReadoutActual (single place)
`thetaNormReadL = actualC3LogShellTensorLogVolumeL - log(actualUnitMassL)`.
It subtracts the unit-ball log mass but does **not** divide by the local degree; there is no
`1/d_F` factor and no `nativeBadLocalWeight` factor.  So this single-place object is a
**dimension-unnormalized** readout.

### A1 side
`a1LocalQLog = log mu(qhatLattice) - log mu(O)` (dimension-unnormalized local quantity),
`a1SignedTerm = a1LocalQLog / d_F` (degree-normalized single-place readout),
`productQ_normalizedLog = sum_b a1LocalQLog_b = sum_b d_b log r_b - totalDelta`
(degree-weighted product), with `totalDelta = sum_b d_b a1Delta_b`.

## Consistency verdict

1. **Product level: consistent.** `thetaNormReadProduct` uses `s1915LocalDegree` and
   `s1915ClosedForm`, the same weights as A1's `productQ_normalizedLog_*` and
   `s1915ClosedForm` consumer.  No `nativeBadLocalWeight = 1/[K_w:(F_mod)_v]` appears in the
   new product file, so the old weight mismatch is fixed there.
2. **Single-place level: different normalization.** `thetaNormReadL` is not divided by `d_F`;
   the A1 single-place analog is `a1LocalQLog`, while A1's `a1SignedTerm` additionally divides
   by `d_F`.  For the same region/unit ball one has `a1LocalQLog = d_F * a1SignedTerm`;
   `thetaNormReadL` is unnormalized and must not be equated with `a1SignedTerm` without the
   `1/d_F` factor.
3. **Unit-ball normalization: consistent.** Both sides subtract/divide by the actual unit-ball
   mass; neither assumes `unitMass = 1`.  `Mzk1P0LNormReadoutProductActual` explicitly records
   `unitMass = 1` as NOT CLAIMED, matching A1's use of `mu(O)` rather than a normalized mass.
4. **Object level: not identical.** `thetaNormReadProduct` is the theta-hull readout
   (`s1915HullMass/s1915UnitMass`), whereas A1 `productQ_normalizedLog` is the qhat-lattice
   readout.  Their exact relation is
   `thetaNormReadProduct = productQ_normalizedLog + totalDelta`
   (equivalently A1 `productQ_normalizedLog = s1915ClosedForm - 1 - totalDelta`).
   The C3-L single-place carrier vs global Bad/tensor index mismatch is already recorded in
   `Mzk1P0LNormReadoutProductActual.LGlobalLocalObjectLock`.

## Reuse guidance

- Use `Mzk1P0LNormReadoutProductActual.thetaNormReadProduct_eq_closedForm_sub_one` as the
  **theta-hull** product readout; combine with A1 `totalDelta` to get the qhat-lattice product
  readout (`s1915ClosedForm - 1 - totalDelta`).
- Do not use `thetaNormReadL` as if it were A1 `a1SignedTerm`; either keep it unnormalized or
  multiply/divide by `s1915LocalDegree` explicitly.
- The old `nativeBadLocalWeight` convention is **not** present in the new product fix; only
  `s1915LocalDegree` is used there, so product comparisons with A1 are weight-consistent.

## Bottom line

The new LNormReadoutProduct fix is **weight-consistent with A1** (`s1915LocalDegree`,
`s1915ClosedForm`), and its unit-ball normalization matches A1's `mu(O)` usage. The single-place
`thetaNormReadL` is dimension-unnormalized and differs from A1 `a1SignedTerm` by the `1/d_F`
factor; that difference must remain explicit. No Lean changes made.
