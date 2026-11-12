# S1916: actual arithmetic Haar signed-average identity — exact first missing

Date: 2026-11-01.  Task: prove or precisely isolate

  arithmeticTupleHullUnitLogVolume places tuple
    + Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal
  = (c3ThetaSignedProcession C3).average

(the S1904 reduction, HaarSignedAverageProof.SignedUnitFactorThetaComparison),
then connect back to S1904.  No fake.

## Result

The identity is NOT a consequence of the current in-tree Haar interface for an
arbitrary additive Haar measure mu.  It is exactly a normalization condition on
mu, and the file proves that condition, its uniqueness, and its S1904 form:

1. [PROVED] The unit-factor identity is exactly

     Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal
       = (c3ThetaSignedProcession C3).average,

   and equivalently

     mu (arithmeticTupleCanonicalHull places tuple)
       = ENNReal.ofReal (Real.exp (c3ThetaSignedProcession C3).average).

   So the unit-reference term is not an independent normalization: it cancels
   the relative unit factor and leaves the actual canonical-hull Haar mass.

2. [PROVED] Scaling mu by a positive finite ENNReal c adds Real.log c.toReal to
   the left-hand side and leaves the hull unit volume unchanged.  Therefore:
   * there is a unique normalizing scalar
       s1916NormalizingScalar a
         = ofReal (exp (a - log (mu canonicalHull).toReal))
     making the identity true with signed average a;
   * every other positive finite scalar makes it false;
   * the identity fails for some additive Haar measure (indeed, after any
     solution, scaling by exp 1 breaks it).

   Thus the exact first missing is the source-selected Haar normalization
   (equivalently the canonical-hull mass equation), not a further algebraic law
   on the existing data.

3. [PROVED] The S1916 identity implies S1904's S1904FirstMissing T P for any
   theta hull T and determinant P with the matching C6 hull readout and
   signed-average procession.  Conversely, under nonnegativity of both real
   readouts, S1904's bridge implies the S1916 identity.

## Lean artifacts

Target file:
  tmp/sheaf/xif/paper/S1916HaarSignedAverageActual.lean
  26789 bytes
  SHA256 65086C0CD3D22FBB37C7D792FC1ACE10EB4ABDC7BECD7A35FFCBA83CD1FDD5F4
  compile command:
    lake env lean -R D:/lean -s 65536 -M 8192 \
      tmp/sheaf/xif/paper/S1916HaarSignedAverageActual.lean
  EXIT=0, no warnings, no sorry/admit/axiom; #print axioms only
  [propext, Classical.choice, Quot.sound].

Olean:
  .lake/build/lib/lean/tmp/sheaf/xif/paper/S1916HaarSignedAverageActual.olean
  368848 bytes
  SHA256 4B9CB051AAAB4E5C82B33982FEE817A27E6D7ECDFE5C095A46F8BF70C2739720
  consumer probe tmp/sheaf/xif/paper/_S1916ConsumerProbe.lean EXIT=0.

Upstream tmp file fixed to compile (it was a write-only draft):
  tmp/sheaf/xif/paper/HaarSignedAverageProof.lean
  7802 bytes
  SHA256 13B8B9EDE44DDF519CD67F8505D3CD2AC42302E4FC519A1E6822219D1C670AA3
  EXIT=0 (one unused simp argument warning)
  Olean 122864 bytes
  SHA256 4842C794EFBFD6BF95E47B61DC950D17D28C47B141951C0156A07BC6A725BC51
  Changes: added the missing opens (NumberFieldFinitePlace,
  ProcessionThetaPacketAverageActual, XiFPaper) and fixed the hreal order in
  c6_hnormal_signed_of_missingFactorization.  No mathematical weakening.

S1904 unchanged:
  source SHA256 B31C647468542F44DD1048B9F26DC27AB72997FFCE5C5B2214F0C3E54445EB8F
  olean SHA256 3C5761EC8D3DE0567E12A34FACF59BDD7C6F7980C254D5E19B931432D9B3A7F0

## Boundary

- The identity is not asserted unconditionally; it is named
  S1916FirstMissing and reduced to the explicit Haar-mass normalization.
- The matching T/P hypotheses in the S1904 connection are explicit; this file
  does not construct the source theta hull on the C6 carrier.  That construction
  (or the equivalent source selection of mu) remains the missing source input.
- Not run: full Project build (lake build LeanFormal), comparator acceptance,
  central watchdog queue, independent human review.  This is a delegated
  subagent package; report hashes and exact missing to the parent.
