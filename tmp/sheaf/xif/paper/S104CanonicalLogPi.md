# S104: canonical logPi and boundary-log dependence

Date: 2026-10-29.

## 1. Exact dependence on logPi (proved)

For fixed uniformizer pi, decomposition d = boundaryUnitDecompositionFor pi x,
and two choices logPi, logPi',

  boundaryLogWithFor pi logPi x - boundaryLogWithFor pi logPi' x
    = n • (logPi - logPi').

Thus the boundary log is indeterminate exactly in the chosen scalar logPi.
This is boundaryLogWithFor_logPi_difference.

## 2. p-adic log candidate

log1p(pi) = log(1 + pi), not log(pi).  The p-adic log series is defined near 1;
the uniformizer pi is not of the form 1 + x with x in the maximal ideal, so
log1p does not provide the logarithm of pi.  candidateLog1pPi is recorded only
as a series candidate, not as canonical logPi.

## 3. Exact missing canonical logPi

CanonicalLogPiData requires the uniformizer, its equality, a scalar logPi,
and the propositions that it is log(pi) and compatible with unitLog.
CanonicalLogPiRequired is its nonemptiness; no inhabitant is asserted.

No fake canonical log/sorry/axiom/True/PUnit.
