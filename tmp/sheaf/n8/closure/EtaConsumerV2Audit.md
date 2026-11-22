# EtaConsumerV2 dependency audit

Date: 2026-10-24
Audited file: tmp/sheaf/n8/closure/EtaConsumerV2.lean
SHA256 2117A049C4306DE1400E0326896C067063AE4F5CA13B5EECE67B8B19C04DB68E

Dependencies:
- EtaRssLogShellLine.lean SHA256 A4D7B94828CE64D50471E217C069C165CEEDE1766EB8CBAD0C9F62DA35E7C6C0
- EtaComparisonMapActual.lean SHA256 E6BC1CD2237EF0F21E44991408D65D95DFE8B9BC75714C35247209360AD93018
- EtaQActual.lean SHA256 64CB25604A91AFD9BFA7726097C2B4D92084AD555575A87B1EFD4E1E2FCA899C

## 1. Verdict

EtaConsumerV2 is a NEGATIVE CONTROL, not an eta^q = eta^anab_S consumer.

The Rss carrier EtaRssLogShellLineData has all fields fixed by equality fields:

  shell = (nativeLocalShell X).logShell
  volumeIndex = logShellVolumeConsumer.index
  logVolume = Real.log volumeIndex

It is therefore a subsingleton.  EtaComparisonMapActual proves both
- etaRssLogShellLineData_subsingleton, and
- etaIndependentComparison_noGo: no nonconstant map Rval -> Rss exists.

Consequently:
- EtaComparisonV2 is an equality of two copies of the same constant map
  (etaQ_etaAnab_square).  It has no comparison content.
- etaComparisonV2_nonconstant_noGo is a real no-go for nonconstancy on this
  fixed-shell carrier, but it does not establish any source eta comparison.
- The Q <= Theta conclusion in EtaConsumerV2 is obtained from
  PaperQLeThetaReduction.paperQLeTheta / paperC9Comparison, i.e. the old
  P6/Values route.  The eta data only supplies Q < 0 through the named
  calibration etaQScalar = qPilotSignedLog.
- The named gaps EtaQCalibrationV2 and EtaV2QNormalizedIdentification are
  unproved; neither is evidence for the eta comparison.

Therefore EtaConsumerV2 must not be cited as an eta-route proof of Q <= Theta.

## 2. Why fixed-shell Rss is not the varying-region Rss

The intended Rss/log-shell side varies with the admissible region and its
reference.  The current carrier fixes:
- shell to the single native log-shell;
- volume index to the single production consumer index;
- log volume to log of that index.

A varying-region Rss must carry at least:
- the admissible region/reference data (P6L.Adm-style actual region pair),
- its varying real log-volume coordinate (not a fixed index),
- a nontrivial comparison structure allowing nonconstant maps from Rval.

Until such a carrier exists, nonconstancy cannot be assumed or derived; the
current no-go only says nonconstancy is impossible on the fixed carrier.

## 3. Dependencies that must be replaced

1. EtaRssLogShellLineData -> an actual varying-region Rss carrier
   (region/reference varying, log-volume read from the region, not fixed).
2. EtaComparisonMapActual.etaQMap/etaAnabMap -> actual etaQ/etaAnab source maps
   on that varying carrier; no canonical constant map.
3. EtaComparisonV2 -> comparison of those actual maps; nonconstancy must be
   derived from the varying carrier, not imposed as an unsourced guard.
4. PaperQLeThetaReduction.paperQLeTheta -> must be removed from any eta-route
   claim, or explicitly labeled as the independent old P6 route.  An eta
   consumer must prove the normalized comparison from the eta maps/calibration,
   not import the paper P6 inequality.
5. EtaQCalibrationV2 and EtaV2QNormalizedIdentification -> exact named source
   gaps; they are not proofs.  Actual q calibration must be proved from the
   native q-unit/value-group data, and Q identification from the actual q
   readout.
6. Audit guards Theta != 0 / Values != {0} / reference != region are NOT used by
   EtaConsumerV2; they must not be reintroduced as free conditions.  If used,
   they must come from the actual guard families and still cannot substitute for
   the eta comparison.

## 4. Correct labeling

- EtaConsumerV2: negative control.  Do not cite as eta^q = eta^anab_S or as an
  eta-route derivation of Q <= Theta.
- Its only valid content: on the fixed-shell subsingleton Rss, any comparison
  map is constant and the conditional Q <= Theta consumer depends on the named
  calibration/Q-id gaps plus the old P6 route.
- No Lean target is changed by this audit.  The Lean declarations remain as
  previously reported, with the above interpretation.

## 5. Next actual steps

1. Construct the actual varying-region Rss carrier from the P6 admissible
   reference/region data; prove it is not a subsingleton.
2. Construct actual etaQ/etaAnab maps on that carrier from the native q-value
   group and the log-shell region; prove the comparison and derive nonconstancy
   if real.
3. Prove the q calibration from the actual native q-unit/value-group norm
   degree, not as a free Real equality.
4. Only then replace the old PaperQLeTheta dependency by the eta-normalized
   comparison.  Until then, any Q <= Theta claim is P6-route, not eta-route.
