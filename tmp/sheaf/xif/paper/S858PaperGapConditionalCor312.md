# S858: PaperGap and conditional Cor312 interface

Date: 2026-10-30. Paper-faithful conditional theorem; no unconditional claim.

## PaperGapIntrinsicVolume

Fields:
* D : SourceLogShellDatum;
* rootUnit : D.Units;
* volumeLog : D.K ->+ Real;
* root_value_eq:
    volumeLog ((D.logMap rootUnit).toAdd)
      = -(order/(2l) * log p);
* hull_log_eq_root:
    paperLeastLambdaOHullLog T b Measure.addHaar
      = volumeLog ((D.logMap rootUnit).toAdd).

This is the intrinsic log-shell normalization datum: V(root) has the paper
negative sign and the least-hull normalized log is that root volume.

## PaperGap(P)

Fields:
* signed_hull_log_eq:
    P.signedHullLogVolume = paperLeastLambdaOHullLog T b Measure.addHaar;
* intrinsic : PaperGapIntrinsicVolume.

No inhabitant is asserted.

## Actual chain links used

* paperGap_hull_eq_S797: least hull = S797 corrected least hull (rfl).
* paperGap_qPilot_subset: S790 paperStackQPilotRegion subset least hull,
  via S810 corrected region and S799 least-hull containment.
* s858SourceLink / s858Inclusion: actual PaperXiFSourceLink/Inclusion from
  the gap's signed log equality plus source identifications, qPilot-paper
  equality, link identification and hlink.

## paperCor312_of_gap

Given h : PaperGap P, [Nonempty label], source identifications, S669 qPilot
equality, link_identification, link implication and hlink, and actual finite
IPL/SHE/APT links, the theorem constructs s858Inclusion P O C3 and applies
paperAssembly_cor312Conclusion, yielding

  Cor312Conclusion
    ((paperCertificate (I := paperXiFInput J)).toContract
      (paperSignedLinkEvidence (I := paperXiFInput J) links)).

The gap h is an explicit assumption, not faked and not an axiom.
