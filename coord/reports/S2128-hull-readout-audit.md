# S2128: hull/logVolume readout audit

Date: 2026-11-02. Layer O; consumer S2040 paper 3.12 / hull direction.

## Actual in PaperSignedHull

- ambient_hull_logVolume_lt_top: hull log-volume finite;
- signedHullLogVolume_le_neg_image_toReal: H <= -vol(image);
- signedHullLogVolume_nonpos: H <= 0;
- signedHullLogVolume_eq_neg_average under the structure field
  hull_logVolume_eq_average.

## S2040ActualThetaLink312

paper312_inequality (and link_implies_inclusion) is a theorem only for an
inhabitant L : S2040ThetaLink312 O Opaper P.  No inhabitant is asserted.
The exact missing chain is S2040FirstMissing:

1. four paper q-pilot identifications;
2. qPilotLogVolume = Real.log q;
3. actual log-theta-lattice displacement data;
4. paper hull normalization P.signedHullLogVolume = Real.log rootStackTheta.

Thus Q <= H is conditional on S2040ThetaLink312/S2040FirstMissing, not
unconditional on the PaperSignedHull interface.

## S2030

S2030 gives an unconditional numerical 3.12 inequality for a different
actual determinant/hull datum (s1940PaperLStarDeterminant / s1902ActualThetaHull),
not the S2040 paper O/Theta-link target.  It is a cross-check, not a substitute.

## New Lean file

tmp/sheaf/xif/paper/S2128HullReadoutActual.lean
SHA256 ECB5ADA3A2A9C822BC8DF874CC515495DA188795ABFCA77211B5F04054EF9065
EXIT=0
olean SHA256 B21D74C6DE4625E7F42221028C04875C69F61A4777907E010171FCD5C598CDBA
size 22864
axioms propext, Classical.choice, Quot.sound.

Theorems:
- s2128_ambient_hull_logVolume_lt_top
- s2128_signedHull_le_neg_image_toReal (H <= -vol(image))
- s2128_signedHull_nonpos
- s2128_qPilot_le_signedHull_of_normalization (Q <= H from the exact
  qPilot <= log Theta comparison plus H = log Theta; no inhabitant).

## Exact first missing

For the unconditional Q <= H on the S2040 actual object:
S2040FirstMissing, specifically the paper hull normalization
P.signedHullLogVolume = Real.log rootStackTheta and the actual O/Theta-link
displacement.  No fake, no assumed S2040ThetaLink312 inhabitant.
