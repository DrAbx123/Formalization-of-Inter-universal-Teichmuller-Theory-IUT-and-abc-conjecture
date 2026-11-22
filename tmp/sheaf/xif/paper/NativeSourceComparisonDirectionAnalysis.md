# Native source comparison: direction and sign analysis

Date: 2026-10-28. Analysis only.

## Actual signs

Paper Theta-pilot hull log-volume (actual Haar candidate):

  paperBadThetaPilotHullLogVolume T b
    = Real.log (paperThetaPilotHullVolume T b).toReal
    = -|log Theta_b|.

Hence the paper magnitude is

  nativeBadThetaPilotHullLogMagnitude T b
    = -paperBadThetaPilotHullLogVolume T b
    = |log Theta_b|.

The native normalized q-pilot magnitude is positive:

  nativeGlobalQPilotMagnitude T = |log q|.

## Corollary 3.12 direction

Corollary 3.12:

  -|log Theta| >= -|log q|.

Multiply by -1 and reverse the inequality:

  |log Theta| <= |log q|.

In the native global candidates this is

  nativeGlobalThetaPilotHullLogMagnitude T
    <= nativeGlobalQPilotMagnitude T.

## Corrected Prop

  NativePaperSourceComparison :=
    nativeGlobalThetaPilotHullLogMagnitude T
      <= nativeGlobalQPilotMagnitude T.

The earlier direction qPilotMagnitude <= thetaHullMagnitude was the reverse of
Corollary 3.12 and has been corrected.

The comparison is not proved: the actual Haar hull volume still lacks the
mono-analytic unit-region normalization and compactness data.  The exact
obstruction is NativePaperSourceComparisonThetaHullObstruction.
