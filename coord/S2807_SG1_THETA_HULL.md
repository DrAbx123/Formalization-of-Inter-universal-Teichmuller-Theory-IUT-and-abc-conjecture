# S2807 — SG1 theta-hull volume identity

Date: 2026-11-07
Status: **ACTUAL**

## File

`tmp/sheaf/xif/paper/S2807ThetaHullVolumeIdentityActual.lean`

```text
src 4899 B
SHA256 258156482fe432b97a507e91aaf014aa5f8b161d391240b5a2c1f1f9fc7280ed
olean 98000 B
SHA256 2e82b066802e18b4b0140ab7f64570a538c5d612776214c4e25caa6ed0cbfdc3
EXIT=0
AXIOMS [propext, Classical.choice, Quot.sound]
QUEUED
```

## SG1 identity

```lean
theorem S2807_thetaHullVolume_eq_haarRegion :
    S2717ThetaHullLogVolume R ... D =
      - (haarLogVolume
          (actualC3LogShellTensorHaar (S2717C3 R ... D))
          (actualC3LogShellTensorRegion (S2717C3 R ... D))).toReal
```

Interpretation: the S2717 theta-hull log-volume is exactly the negative actual
Haar log-volume of the C3 log-shell tensor region.  The proof unfolds
`S2717ThetaHullLogVolume`, `globalThetaHullInterface`, `globalThetaLogVolume`,
rewrites by `globalThetaHull_eq_imageSet`, and closes definitionally.

## Consumer: paper target as three Haar-region inequalities

```lean
theorem S2807_paperCor312Full_iff_haarRegion
    (v : FinitePrimePlace 2 7)
    (logQ dmod dFpd fFpd eStar etaPrm : Real) :
    PaperCor312Full R ... D v logQ dmod dFpd fFpd eStar etaPrm ↔
      S2717QPilotLogVolume R ... ≤
        -(haarLogVolume (actualC3LogShellTensorHaar ...) 
            (actualC3LogShellTensorRegion ...)).toReal
      ∧
      -(haarLogVolume ...).toReal
        ≤ CThetaPaper fiveLabel logQ dmod dFpd fFpd eStar etaPrm *
            paperQAbsLog fiveLabel logQ
      ∧ -1 ≤ CThetaPaper fiveLabel logQ dmod dFpd fFpd eStar etaPrm
```

This is the exact SG1 reduction of the paper target: only the middle inequality
(the theta-hull upper gap) remains analytic.

## Notes

- No hdeg / `SourceImageRealization` dependency; SG1 is on the S2717 route.
- No ABC assumption, no fake object, no axiom beyond the permitted trio.
