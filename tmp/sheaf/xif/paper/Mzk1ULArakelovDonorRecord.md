# Arakelov donor record (F1/F8/D1/D4)

Date: 2026-11-17. Author: andrew (lane L-H). Status: reference only, no Lean port.

## Search performed (Lead reuse rule)

Keywords: `Arakelov`, `arakelov`, `divisorHeight`, `logHeight`, `frameHeight`,
`pushforward.*height`, `height.*pushforward` in:
- `tmp/external` (12122 hits; mostly flt-lean AlgebraicCurve/Annulus/abv machinery),
- `tmp/lana-port-src` (157 hits), `tmp/n8-20261018` (2 hits, no height machine),
- `tmp/mathlib4-4.36.0-rc2/Mathlib` (200 hits; `NumberTheory/Height/Projectivization.lean`
  is the same as the pinned 4.32 file we already use; no new frameHeight/Arakelov lemma).

## Donors found (not ported)

1. `tmp/lana-port-src/Iut/Arakelov/LineBundle.lean`: arithmetic line bundles and the
   normalized Arakelov degree (`ArithLineBundle`, `degNorm_eq`, `finDeg_eq_ordp`).
2. `tmp/lana-port-src/Iut/Arakelov/QPilot.lean`: `qDivisor`, `degNorm_qDivisor :
   (qDivisor D).degNorm = D.qPilot.logQ`, `lhs_eq_neg_degNorm_qDivisor`, and the
   `K`-side `degNorm_qPowDatum`.  The proof unfolds the normalized degree as
   `Σ_w (f_w/[F:Q])·ord_w(q_w)·log p_w`.
3. `tmp/lana-port-src/Iut/Arakelov/Container.lean`: Arakelov degree vs log-volume.
4. `tmp/external/flt-lean/Theorems/Thm_AlgebraicCurve_Annulus_abv_*`: nonarchimedean/
   archimedean `abv`/`evalAt` estimates of the same shape as `Mzk1G1F8LocalActual`
   (`fermat_local_nonarch`, `fermat_local_arch`); cross-check only.

## Why not ported

`QPilot.lean` imports `Iut.Arakelov.Container`, which imports `Iut.Wall.QPilotRegion` and
`Iut.Arakelov.LineBundle`; `LineBundle.lean` imports `Iut.Concrete.LocalConstruct.Integral`,
which imports `Iut.Concrete.LocalConstruct.Packet`; `QPilotRegion.lean` imports
`Iut.Wall.IdentifiedCopies`; the closure is >10 external Iut subtree files and the objects
(`InitialThetaData`, `ArithLineBundle`, `QPilotData`, `tateParam`, `badPlacesOver`) do not
match the route objects.  Lead ruling 2026-11-17: do not port Lean; use the v2 q-pilot
normalized sum instead.

## Replacement used

- `Mzk1ULQPilotMagnitudeV2Actual.qPilotMagnitudePaper_v2` (DONE 2026-11-16 21:55:33,
  three axioms): the normalized sum `(1/[F:Q])·Σ_b Σ_{P|b} f_P·c_P·log p_P`;
- `Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2 = qPilotMagnitudePaper_v2/(2*l.value)`.

Correspondence: `degNorm_qDivisor`'s unfolded RHS and `qPilotMagnitudePaper_v2` are
term-by-term the same normalized sum over bad places (place weight = inertDeg/finrank,
`ord` = q-order, `log` of residue characteristic); `M_paper` is the `1/2ℓ` normalization
used in C4.  If a later step needs an Arakelov-specific identity, prove it for the v2
real-valued sum, not by importing the external package.