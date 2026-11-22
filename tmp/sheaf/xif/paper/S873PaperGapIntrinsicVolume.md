# S873: actual PaperGapIntrinsicVolume fields

Date: 2026-10-30. All fields except the hull-log equality are actual.

## SourceLogShellDatum instance

gapLogShellDatum:
  p := qVFamTensorP T b;
  hp := Fact.out;
  K := Real;
  Units := StackSectionCarrier T b;
  invariants := top;
  logMap := stackDivisorLogMap (u |-> u.2).

stackDivisorLogMap : StackSectionCarrier T b ->* Multiplicative Real
is the S782 divisor coordinate; map_one/map_mul are rfl.

## volumeLog

gapVolumeLog : Real ->+ Real, x |-> -x * log(qVFamTensorP T b).
Additivity is the AddMonoidHom map_add proof; no fake.

## rootUnit and root value

gapRootUnit := stackRootSection T b.

gapRoot_value_eq:
  gapVolumeLog ((gapLogShellDatum.logMap gapRootUnit).toAdd)
    = -(order/(2l) * log p).

This uses the actual S782 stackRootSection divisor order/(2l).

## Single exact field

S873HullLogExactGap:
  paperLeastLambdaOHullLog T b Measure.addHaar
    = gapVolumeLog ((gapLogShellDatum.logMap gapRootUnit).toAdd).

paperGapIntrinsicVolumeOfHullLogEq h : PaperGapIntrinsicVolume
fills D, rootUnit, volumeLog, root_value_eq from the actual data and only
hull_log_eq_root := h.

## Conditional proof of the single field

s873HullLogExactGap_of_data, for
data : ArithmeticTuplePureFractionalScalingData ... paperRootCoefficientFamily,
uses S799 paperLeastLambdaOHullLog_eq_formula (the S822 fractional-lattice
normalized-log formula) and the Unit sum to prove the hull-log equality.
paperGapIntrinsicVolume_of_data then builds the full intrinsic volume.

Without this scaling data, S873HullLogExactGap is the exact single field.

No fake hull-log equality; no axiom.
