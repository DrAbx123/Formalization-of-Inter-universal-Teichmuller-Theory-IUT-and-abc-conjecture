# Native q-pilot / paper Theta-pilot shared-source check

Date: 2026-10-28. Analysis only; no compilation.

## Conclusion

NativeGlobalQPilotNormalizedLogVolumeActual and
PaperThetaPilotCarrierActual use the SAME native source object:

- same parameter T : SourceNativeInitialThetaData l;
- same bad index Bad (nativePlaceSelection T);
- same actual base q candidate baseQ T b at nativeBaseSectionPlace T b.

No different q source and no I.initial.badPlaces equivalence is used.

## Exact shared data

Native q-pilot normalization (NativeGlobalQPilotNormalizedLogVolumeActual):

  nativeBadToFPlace T b       = (nativeBadLift T).lift b
  nativeBadLocalWeight T b    = localNormalizedWeight T.arithmetic (nativeBadToFPlace T b)
  baseQ T b                   = nativeBaseQFamily T b
  baseQLogMagnitude T b       = -log ||(baseQ T b).q||.

Paper Theta-pilot carrier (PaperThetaPilotCarrierActual):

  paperBaseQReal T b          = ||(baseQ T b).q||
  paperThetaValue (paperBaseQReal T b) j = (||(baseQ T b).q||)^(j^2)
  paperBadThetaPilotHull T b  = holomorphicHull at paperBaseQReal T b.

Thus the Theta-pilot hull is evaluated at the same native q candidate
baseQ T b; its real q is the norm of that candidate.

## Alignment theorems

NativeGlobalQPilotThetaPilotAlignmentActual.lean proves:

- sharedBaseQLogMagnitude_eq:
    baseQLogMagnitude T b = -log ||(sharedNativeBaseQ T b).q||
  where sharedNativeBaseQ T b = baseQ T b;
- sharedPaperBaseQReal_eq:
    paperBaseQReal T b = ||(sharedNativeBaseQ T b).q||;
- sharedNativeQPilotLocalMagnitude_eq:
    nativeQPilotLocalNormalizedLogMagnitude T b
      = nativeQPilotLocalNormalizedWeight T b
        * (-log ||(sharedNativeBaseQ T b).q||).

## Caveats

- The paper Theta-pilot hull has an actual Haar volume candidate, but the
  mono-analytic unit-region normalization/compactness is still the separate
  PaperThetaPilotHullNormalizationRequired obstruction.
- The q-pilot normalization uses actual native bad weights and F_l^x average;
  it does not use I.initial.badPlaces.
- No comparison inequality is asserted here.
