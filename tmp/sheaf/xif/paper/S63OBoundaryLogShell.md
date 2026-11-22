# S63: O-boundary and the integral log-shell carrier

Date: 2026-10-29.

## Source log-shell carrier

sourceLocalLogShellDatum (Kummer.SourceLocalLogShellDatum) has

  Units = (Integers (CommonPrimeCompletion place))^x
  logMap = unitLogHom
  logShell = integralLogShell.

Thus the actual log-shell is built from O-times, the unit group of the norm
valuation ring.  It is not built from O-triangle (integral monoid including 0)
or from O-boundary (nonzero integral elements).

## Actual S63 construction

* sourceLogShellUnits_eq_integralUnits: the carrier is
  (Integers (CommonPrimeCompletion place))^x;
* sourceOBoundaryMonoid = {x | x in Integers L and x != 0}, an actual
  Submonoid of the completion;
* sourceOTimesToBoundary: actual map O-times -> O-boundary.

## Exact gaps

* CompletionIntegersEqIntegers: S56 used the number-field completion integral
  ring CompletionIntegers; the log-shell uses the norm valuation ring Integers.
  Their equality is recorded, not assumed.
* OBoundaryLogShellGap/OBoundaryLogShellRequired: the log-shell has no
  logarithm on all of O-boundary; only the O-times unit map is available.

No fake equality/sorry/axiom/True/PUnit.
