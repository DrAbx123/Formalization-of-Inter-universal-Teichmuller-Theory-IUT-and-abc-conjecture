# S300: actual DVR decomposition and general factor gap

Date: 2026-10-29. Object-first; no inequality.

## Proved

exists_unit_uniformizer_zpow: every field unit lambda admits an actual DVR
decomposition

  lambda = Units.map (algebraMap (Integers L) L) u * rootUniformizerField ^ n

with n : Int and u a unit of the integer ring.  This is the actual decomposition
needed for the general lambda factor.

## Remaining exact requirement

The general norm formula

  rootHaarFactor lambda = ofReal(||lambda||^d),

and its block transfer, still require the norm/zpow arithmetic after this
decomposition.  They are recorded as RootHaarFactorNormPowGap/Required and
BlockHaarFactorNormPowGap/Required, with no inhabitants.

No fake factor/sorry/axiom/True/PUnit; no inequality.
