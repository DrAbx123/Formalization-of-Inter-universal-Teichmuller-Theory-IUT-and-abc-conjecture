# O2 paper readout: normalization and explicit exponent counterexample

Date: 2026-10-25. Owner: logdescent. Lean: O2PaperReadoutActual.lean.
Compile: lake env lean -j1 -R D:/lean -> EXIT=0, zero sorry.

## Actual normalization

- PaperThetaQ = -log ||q|| for actual ClauseB FinitePlaceQCandidate q.
- PaperThetaAnab = log(logShellVolumeConsumer.index).
- NormalizedThetaQ := q.order * log(residueNormBase place).
- normalizedThetaQ_eq_thetaQ: NormalizedThetaQ = PaperThetaQ (actual order/
  exponent formula).
- PaperThetaAnab_nonneg: ThetaAnab >= 0 (actual index positive).
- o2PaperComparison_iff_thetaAnab_eq_normalized: the O2 comparison is exactly
  ThetaAnab = q.order * log(residueNormBase).

## Explicit different-exponent counterexample

- powTwoCandidate := (W.q).pow 2.
- thetaQ_powTwoCandidate: ThetaQ(q^2) = 2 * ThetaQ(q).
- not_both_q_and_powTwo_compare: if q satisfies the paper comparison, q^2
  cannot satisfy it with the same ThetaAnab (because ThetaQ(q)>0).  ThetaAnab
  depends only on the F-place, so an arbitrary q candidate makes the readout
  non-canonical; the normalization/exponent must be fixed.

No arbitrary q is introduced: both q and q^2 are actual candidates at the
same selected place.