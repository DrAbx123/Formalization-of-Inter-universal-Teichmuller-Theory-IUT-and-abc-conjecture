# S295: zpow laws and general factor gap

Date: 2026-10-29. Object-first; no inequality.

## Proved

rootHaarFactor_one, rootHaarFactor_inv, rootHaarFactor_zpow:

  rootHaarFactor (lam ^ n) = rootHaarFactor lam ^ n for n : Int,

with negative n handled via the inverse factor and zpow_negSucc.

## Remaining exact requirement

The general lambda norm formula

  rootHaarFactor lam = ofReal(||lam||^d)

requires the actual DVR decomposition lam = u * pi^n (u of norm one) and the
norm/zpow calculation; it is recorded as RootHaarFactorNormPowGap/Required with
no inhabitant.  The uniformizer/prime cases are already proved in S290.

No fake factor/sorry/axiom/True/PUnit; no inequality.
