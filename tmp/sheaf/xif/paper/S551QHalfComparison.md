# S551: thetaUnitActual vs S546 qHalfRoot

Date: 2026-10-29. Actual comparison for the 2l-th roots; exact mismatch for
qHalfUnitActual.

## Actual comparison

qHalfRootActual := S546 qHalfRoot specialized to the actual F-side qVFamily
parameter at FPlace T b.

QHalfComparisonData:
* thetaUnit := thetaUnitActual (S532), theta_pow: thetaUnit^(2l)=qUnit;
* qHalfRoot := qHalfRootActual, qHalfRoot_pow: qHalfRoot^(2l)=qUnit;
* ratio := thetaUnit / qHalfRoot;
* ratio_mem_mu: ratio ∈ rootsOfUnity (2l) (ACF T b), by S546
  qHalfRoot_ratio_mem_rootsOfUnity.

qHalfComparisonData is the actual instance.

## Exact mismatch for qHalfUnitActual

S532 qHalfUnitActual is thetaUnit^l, so it satisfies
  qHalfUnitActual^2 = qUnit,
not qHalfUnitActual^(2l)=qUnit.  It is a square root, not a 2l-th root, so the
mu_{2l} ratio theorem does not apply to qHalfUnitActual itself.

S532QHalfUnitVs2LRootGap records qHalfUnitActual^2=qUnit;
S532QHalfUnitVs2LRootGap_holds proves it; l_value_ne_one records l≠1.

No fake equality; no completion 2l-root; no L.
