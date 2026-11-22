# A1 product signed readout vs new L-side normalization/product readout — reuse note

Date: 2026-11-14. Lane: stage4. **Read-only note; no Lean file was modified or added.**

## Files inspected

- `tmp/sheaf/xif/paper/Mzk1P0QThetaReadoutCorrespondenceActual.lean` (green 00:34:54Z)
- `tmp/sheaf/xif/paper/Mzk1P0QThetaReadoutNormCorrectionActual.lean` (green 00:57:51Z)
- `tmp/sheaf/xif/paper/Mzk1P2QHatNormAgreementUnconditionalActual.lean` (green 23:27:06Z) and `Mzk1P2QReadoutUnconditionalActual.lean` (green 23:31:02Z)
- `tmp/sheaf/xif/paper/Mzk1A1DeltaExplicitActual.lean`, `Mzk1A1QhatSaturationReadoutActual.lean`, `Mzk1A1SignedReadoutProductActual.lean` (A1 side)

## Same origin

`Mzk1P0QThetaReadoutCorrespondenceActual.qhatLogReadout T b` is defined as
`(1/d_b)(log mu(c0QLattice_b) - log mu(O_b))`, which is **definitionally the same** as
`Mzk1A1DeltaExplicitActual.a1SignedTerm` (A1 local signed readout) and equals
`a1LocalQLog / d_b`.  The green theorem
`Mzk1P0QThetaReadoutCorrespondenceActual.a1LocalQLog_eq_degree_qhatLogReadout`
states exactly `a1LocalQLog = d_b * qhatLogReadout`.

The product identity is also the same origin: both use
`Mzk1P3ProductHaarPiActual.productNormalizedLog_pi` on `c0ProductQ = pi_b c0QLattice_b`
and the same local Haar measures.

## L-side results and their A1 counterparts

| L-side | A1 side | Relation |
|---|---|---|
| `qhatLogReadout_eq_log_norm` / `qhatLogReadout_eq_neg_abs_log_norm` | `a1SignedTerm_eq_log_radius_sub_delta` | Same local measure object; L-side additionally uses `qhatHaarScaling_actual` from S865 to replace `(log mu(c0Q)-log mu(O))/d` by `log||qhat||`. |
| `c0ProductQ_normalizedLog_eq_sum_qhat_actual` | `productQ_normalizedLog_eq_sum_a1LocalQLog` | Both equal `sum_b (A_b-B_b)`; L-side rewrites each term to `d_b log||qhat_b||`, A1 keeps measure logs and then subtracts `totalDelta`. |
| `sum_degree_qhatLogReadout_le_closedForm_sub_one` | `productQ_normalizedLog_le_closedForm_sub_one` | Same inequality; L-side via `log||qhat||`, A1 via `log r_b - a1Delta_b` and `totalDelta >= 0`. |
| `qhatLogReadout_eq_log_norm_of_scaling` | `signedReadout_eq_log_radius_sub_delta` | L-side conditional form before `qhatHaarScaling_actual` was proved; A1 never needed the norm-scaling law. |

## Norm correction (new, not in A1)

`Mzk1P0QThetaReadoutNormCorrectionActual.qhatLogReadout_sub_paperQ_eq_log_ratio`
proves, under the explicit norm-instance agreement
`||c0QHat_b|| = qVFamNormalizedNorm_b`, that
`qhatLogReadout_b - paperQSignedReadout_b = log(qVFamNormRatio_b)`.
This is a **paper-q normalization correction not present in the A1 signed readout**; it is
the reason the new L-side can speak about the paper q while A1 only speaks about the actual
qhat/lattice readout.  The degree-weighted form
`qhatLogReadoutDegreeGlobal_sub_paperQ_eq_sum_degree_log_ratio` uses the same weights as A1.

## Reusability verdict

- **Same origin: yes.** The qhat/measure component is definitionally identical; no duplicate
  mathematical object is introduced.
- **Reusable by A1:** the L-side file supplies an unconditional `qhatHaarScaling_actual` and
  `qhatLogReadout_eq_log_norm`; A1 can import them to restate its measure readout in norm form
  (`signedReadout = log||qhat||`), and to derive the closed-form inequality without the
  norm-scaling gap that A1 deliberately avoided.
- **Reusable by L-side:** `Mzk1A1SignedReadoutProductActual.productQ_normalizedLog_eq_closedForm_sub_one_sub_totalDelta`
  gives the explicit `totalDelta = sum_b d_b a1Delta_b` decomposition; L-side's
  `sum_degree_qhatLogReadout_le_closedForm_sub_one` is the same inequality with `totalDelta`
  hidden.  A1's `a1LocalQLog_eq_degree_qhatLogReadout` already links the two conventions.
- **Do not merge blindly:** (i) L-side's `nativeBadLocalWeight = 1/[K_w:(F_mod)_v]` weights
  differ from A1's `s1915LocalDegree` weights; use the degree-weighted L-side definitions
  (`qhatLogReadoutDegreeGlobal`, `paperQSignedReadoutDegreeGlobal`) when matching A1/closedForm.
  (ii) The paper-q norm correction is conditional on `||c0QHat|| = qVFamNormalizedNorm`; it is
  not part of the A1 measure identity and should not be silently dropped.

## Bottom line

The new L-side normalization/product readout is **the same qhat/measure source as A1**, with
the extra unconditional norm identification from `qhatHaarScaling_actual` and the paper-q
norm-ratio correction.  It is reusable in both directions; the only non-shared inputs are the
paper-q norm agreement and the different weight convention.  No Lean changes made.
