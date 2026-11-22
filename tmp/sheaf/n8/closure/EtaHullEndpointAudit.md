# Eta hull endpoint audit: Q <= h vs Q <= Theta

Date: 2026-10-24. Node: n8-c9-output-region-source-route / eta hull route.
Status: audit only; no closure. target_accepted = false.

## Question

The recent numeric endpoint result is

  Q = qORegionLogVolume X = qPilotSignedLog X < 0,
  h = arithmeticTupleHullUnitLogVolume places tuple >= 0,
  hence Q <= h as real numbers.

This audit decides whether h is the actual P6 target Theta (ValuesBounded/Theta
route), or only a donor on a different carrier / with a different normalization,
and therefore whether Q <= h may be consumed as Q <= Theta.

## Verdict

**Donor / different carrier / different normalization. Q <= h must NOT be used
as Q <= Theta.**

There is no production theorem identifying
arithmeticTupleHullUnitLogVolume with the P6 output readout or with Theta.

## Evidence from the actual definitions

### 1. What arithmeticTupleHullUnitLogVolume is

File: LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceArithmeticTupleHullVolume.lean

- Carrier: ArithmeticTensorTupleBlock places tuple.
- Value: normalizedLogVolume Measure.addHaar
    (hull (arithmeticTupleFieldLogImage places tuple e))
  after a field-product decomposition
    e : ArithmeticTensorTupleBlock places tuple ≃ₐ[Q_p] ((j : J) → E j).
- Normalization: normalizedLogVolume (unit region has log-volume 0; the value is
  nonnegative by arithmeticTupleHullUnitLogVolume_nonneg).
- It is a unit-relative tensor-hull volume, constructed to support the C6/IQ hull
  interface. It is not defined as a P6 output ell_out, not defined as Theta, and
  it is not tied to a source-allowed output J in P6Comparison.

### 2. What the P6 target actually is

File: tmp/sheaf/n8/closure/P6Comparison.lean

- SourceAllowedOutput.region is the actual T11 theta-image set
    { y | exists c : Choice n x, y = T.thetaImage n c }.
- SourceAllowedOutput.hullPoss is
    J.region ⊆ J.B.hull,
  where B : C6ActualIQData C3.tensorPlaces C3.tensorTuple mu.
- SourceAllowedOutput.ellOut is
    J.B.normalizedLogVolume J.region,
  on the C6IQCarrier, not on the arithmetic tensor tuple block used by
  arithmeticTupleHullUnitLogVolume.
- P6Exact/P6Epsilon quantify over SourceAllowedOutput X and use ellOut/Q only.
  They do not contain arithmeticTupleHullUnitLogVolume, and they do not contain
  Theta.

Therefore even a numeric inequality Q <= arithmeticTupleHullUnitLogVolume is
not a statement about ellOut or about Theta.

### 3. What Q is

File: tmp/sheaf/n8/closure/EtaQRegionRepresentation.lean and
EtaVaryingCalibrationQOActual.lean

- Q = qORegionLogVolume X = log ||(C9QPilotRegion.nativeQ X).q||
  = qPilotSignedLog X, on the native qO completion.
- Q < 0 (qPilotSignedLog_neg).

The arithmetic tensor hull h lives on ArithmeticTensorTupleBlock; qO lives on
Completion (nativeFPlaceOverBad X). Equality of the two as real numbers is not
an identification of carriers.

### 4. The Theta/Values consumer

File: tmp/sheaf/n8/closure/EtaGlobalObstructionGuard.lean

GlobalObstructionData carries arbitrary real h, Q, Theta, Nat degA/degZ,
kappa/S and the source bound h <= Theta. Its consumer requires

  kappa = 0 or S >= kappa

and only then derives Q <= Theta.

Nothing in the hull-volume file constructs GlobalObstructionData, actual A, Z,
kappa, S, or h <= Theta. Supplying Theta := arithmeticTupleHullUnitLogVolume
would be an arbitrary identification, not a production consumer.

## Consequence for the current route

- Q <= h is a valid numeric donor inequality only.
- It is not Q <= ellOut(J), not Q <= Theta, and not a P6 ValuesBounded result.
- Even if one identified h with Theta, the global Q <= Theta consumer still
  needs actual A/Z and kappa=0 or S>=kappa (CLOSURE-GUARD G1-G7); the endpoint
  inequality alone is insufficient.
- A local collection/existence or local comparison still cannot be promoted to a
  global Q<=Theta bound (C9 local-global counterexample).

## Exact missing declarations for an actual alignment

To upgrade the donor to an actual target, one of the following must be proved
with production definitions:

1. Carrier/readout alignment:
   arithmeticTupleHullUnitLogVolume places tuple
     = SourceAllowedOutput.ellOut J
   for the actual source-allowed output J built from the T11 theta image and C6
   actual IQ hull (same carrier C6IQCarrier and same normalization).
2. Or Theta identification:
   arithmeticTupleHullUnitLogVolume places tuple = Theta
   where Theta is the actual P6 ValuesBounded/Theta object, plus h <= Theta from
   the actual source-bound theorem.
3. Or a guarded global consumer with actual A,Z,kappa,S and kappa=0 or S>=kappa.

None is currently supplied. The first two are equality/alignment gaps; the third
is the global descent gap.

## Consumer rule

Consumer must not use:

  qO Q <= arithmeticTupleHullUnitLogVolume h

as a substitute for:

  Q <= Theta   or   P6 Exists J, J.hullPoss and Q <= ellOut J.

No fake closure. No target_accepted. No kernel_closed. No ABC claim.
