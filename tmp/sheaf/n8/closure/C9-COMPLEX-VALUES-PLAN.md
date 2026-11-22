# C9 complex ValuesPaper: object choice and remaining problems

Date 2026-10-23. Adopt the complex/paper-faithful object, not the simple
`thetaImage` singleton value.

## Assumed complex object

`ValuesPaper` = set of possible signed normalized log-volumes of actual
pilot-object output data, after:
1. actual C4 witnessed construction/evaluation (retain `n,x,w` and actual
   output point `w.2.1`, not only the choice label `w.1`);
2. formation of the relevant output region/hull data;
3. determinant/tensor-power bookkeeping;
4. actual normalized log-volume (procession-normalized, Kummer-relative),
   with `+inf` branch where applicable.

This is not `B.normalizedLogVolume {T.thetaImage n w.1}`.

## Current repo objects

- C4: `D.Witness n x = Sigma (Choice) {y // eval ... = y}`; output is `w.2.1`.
- C6/C8: `B.normalizedLogVolume` and `B.signedHullLog` on `C6ActualIQData`
  (canonical hull); actual normalization identity only for the canonical hull.
- T11: `SourceThetaIQInterface` with arbitrary `thetaCompletion/thetaImage`;
  packet identification not proved.
- C7: `sourceHolomorphicHull` and canonical hull; `SourceUToIQDonor`,
  `ThetaImageContainmentDonor`, `QPilotHullMembershipDonor` are named sorries.
- No production map from C4 output data (`w.2.1` / `U`) to the C6 IQ carrier.
- No production determinant/tensor-power computation on output data.
- No actual q-pilot region/log-volume donor; `QPaperScalar` gives only a scalar.
- C9Paper Q/Theta/Values structures currently have free fields; weak.

## Remaining problems (ordered)

P1. C4 output -> IQ map.
    Need actual `toIQ : ThetaPilotPoint v -> C6IQCarrier` (or output-region map)
    compatible with `D.eval`/`D.U`. `SourceUToIQDonor` is exactly this, currently
    a named sorry.

P2. Output-level normalized log-volume.
    Even with toIQ, need the paper output log-volume, not an arbitrary singleton
    normalized volume. Need determinant/tensor-power/procession normalization
    on the output image/region.

P3. Actual H from U.
    Need `paperHolomorphicHull U` and containment; canonical hull is only
    evidence. C7 source-side containment exists for source hull, but no IQ H
    equality/map.

P4. QPaper.
    Need actual q-pilot region and procession-normalized Kummer-relative
    log-volume. Only `QPaperScalar = localSignedLog C3.q` exists; region absent.

P5. ThetaPaper.
    Need normalized Kummer-relative hull log-volume with Ind1/2/3; current
    raw source hull volume and canonical IQ hull are insufficient.

P6. Values membership/boundedness.
    After P1/P2, prove `ValuesPaper ⊆ R<=ThetaPaper` and the approximation
    statement; currently C9Paper has only weak named obligations.

P7. +inf/archimedean.
    Use WithTop Real and a separate archimedean branch; do not collapse top.

P8. Q/Theta Ind asymmetry.
    Q must not consume Ind1/2/3; Theta must. Current interfaces do not encode
    this asymmetry.

## Verdict

Under the complex-object assumption, C9 has at least P1-P8 open; none is a
local missing lemma. The first executable subproblem is P1 (C4 output/U -> IQ
map), then P2/P3. No C9 closure claimed.