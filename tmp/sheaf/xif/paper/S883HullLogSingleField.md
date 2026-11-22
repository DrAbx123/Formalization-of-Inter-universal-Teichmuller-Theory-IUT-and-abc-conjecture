# S883: single-field hull log

Date: 2026-10-30. Actual sign relation + interface alternative; actual field
remains conditional on the minimal scaling datum.

## Actual sign relation

lambdaOLogVolume_eq_gapVolumeLog:
  paperLambdaOLogVolume cRoot
    = gapVolumeLog ((gapLogShellDatum.logMap gapRootUnit).toAdd).

Proof: S864 paperLambdaOLogVolume_cRoot_eq_neg_section gives
  V_lambdaO(cRoot) = -paperIntrinsicLogVolume(root);
S859 paperIntrinsicLogVolume_root evaluates the root volume as
  order/(2l) * log p;
S873 gapRoot_value_eq gives the same with the paper negative sign.

Hence
  s883HullLogExactGap_iff_lambdaO:
  S873HullLogExactGap
    <-> paperLeastLambdaOHullLog = paperLambdaOLogVolume cRoot.

## Interface alternative (not actual Haar)

paperLeastLambdaOHullLogInterface :=
  paperLogVolumeOnHull (paperLeastLambdaOHull).

This uses S872's definitional V_lambdaO: if the set is the least hull it returns
paperLambdaOLogVolume cRoot, else 0.  Theorems:
* paperLeastLambdaOHullLogInterface_eq_lambdaO;
* paperLeastLambdaOHullLogInterface_eq_gapVolume;
* S883HullLogInterface and s883HullLogInterface package this as an interface.

This is explicitly an interface, not a proof that the actual
paperLeastLambdaOHullLog (normalized Haar log of the least hull) equals it.

## Exact minimal data

S883ScalingDataRequired :=
  Nonempty (ArithmeticTuplePureFractionalScalingData ... paperRootCoefficientFamily).

s883HullLogExactGap_of_scalingData proves the actual S873 single field from that
data (via S873/S799/S822).  No no-go is claimed: this is the exact minimal
datum, and the field remains open without it.

S883ActualHullLogStillOpen records the actual field.
