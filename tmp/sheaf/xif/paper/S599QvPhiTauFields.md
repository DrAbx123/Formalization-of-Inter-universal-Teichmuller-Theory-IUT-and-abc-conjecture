# S599: S568 QvPhiQOrderTauInput fields from S575 preimage

Date: 2026-10-29. Fields actual; compatibility explicit; tau conditional.

## Fields

For P : S561MinimalPackage K and qOrder>0,
s599QOrderFields X : QvPhiQOrderFields P.ramification (s566Input P) X.obj
  divisor := (positiveQvPhiPreimage P X.obj qOrder hq).divisor
  rationalFunction := (positiveQvPhiPreimage ...).rationalFunction
  divisor_eq := (positiveQvPhiPreimage ...).divisor_eq.

## Compatibility

S599TauCompatibility records the remaining S568 fields:
pullback_mem, units_commute, multiplication_bijective,
isotropicHull_mem_range.  These are inputs, not fabricated.

## Actual conditional tau

s599QvPhiQOrderTauInput C fills fields from s599QOrderFields and compatibility
from C.
s599TauData C := tauDataOfQOrderInput ...
s599CharacteristicSplitting C := characteristicSplittingOfQOrderInput ...

No fake tau/compatibility; no completion/L.
