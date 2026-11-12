# SUBAGENT C REPORT - Card-HULLREAL signed q-pilot comparison

Date: 2026-11-07
Task: deep-audit group C (task-700), first missing object of Card-HULLREAL
New file: tmp/sheaf/xif/paper/S2981SignedQPilotActual.lean
This report: coord/SUBAGENT_C_REPORT.md
No existing source file was edited. The read-only import of
CardHullRealFinitePhaseGate.lean is used for the phase dichotomy.

## 0. Verdict in one paragraph

The actual q-pilot signed log is supplied as a definition from the source theta
packet: qPilot = -|log q|, equal to -|logDegree of the realized q-parameter| by
the realization field degree_of_q.  The (xi-f) comparison at this actual qPilot
is PROVED UNCONDITIONALLY, but it is vacuous.  The value-realized source hull is
a submonoid and the log-degree is additive, so it is either the collapsed
zero-volume phase or the top phase; in both phases sourceRealHullVolume = 0.
Consequently sourceSignedHullLogVolume = 0 always, and the literal comparison is
qPilot <= 0, true for every source q.  The non-collapsed carrier interface is
proved empty for every realization.  The exact first missing object is therefore
not a numeric bound at the value layer: it is an ambient IQ/O-module carrier on
which the holomorphic hull is a bounded lambda.O region, not the least
scaling-stable value submonoid.  The value-layer O-module normalization
ld(lambda) + C <= |log q| is necessary at a tight point but cannot make the
value hull positive finite.

## 1. Actual q-pilot supplied

Definitions in the new file:

    sourceThetaPacketQ        = (I.theaterAt 0 0).thetaPacket.q
    sourceQPilotLogMagnitude  = |Real.log q|
    sourceQPilotSignedLog     = -|Real.log q|

Proved:

* sourceQPilotSignedLog_eq_neg_abs_logDegree:
    sourceQPilotSignedLog v R =
      -|logDegreeAt 0 0 v (R.posRealAction
          (Multiplicative.ofAdd (Real.log q)))|
  by the realization field R.degree_of_q.
* sourceQPilotSignedLog_neg_iff: qPilot < 0 <-> q != 1.
* sourceQPilotSignedLog_exp_of_q_lt_one: q < 1 -> exp qPilot = q.
* sourceQPilotSignedLog_eq_log_of_q_lt_one: q < 1 -> qPilot = Real.log q.
* No certificate below takes qSigned as a parameter; qSigned is the definition
  above.

Relation to the arithmetic q-family.  The tree also has
ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog on a
number field k.  That quantity lives on the finite-place q-candidate carrier and
no theorem identifies it with sourceQPilotSignedLog.  The source theta-packet
quantity -|log q| is the q-parameter log used by the existing source-level target
of SourceContractionWlogReduction.lean (-|log q| <= -|log Theta|).  The
number-field identification is a separate missing bridge; it is not assumed here.

## 2. Exact reductions (all proved, no sorry)

Define

    SourceXifSignedComparisonAtQPilot I v R n :=
      sourceQPilotSignedLog v R <= sourceSignedHullLogVolume v R n.

Proved:

* sourceXifSignedComparisonAtQPilot_iff_realPart_le:
    comparison <-> sourceRealHullVolume v R n <= |Real.log q|.
  Unconditional; no finiteness hypothesis.
* sourceXifSignedComparisonAtQPilot_iff_hullVolume_le:
    under hfin = sourceHullVolume < top,
    comparison <-> sourceHullVolume <= ENNReal.ofReal |log q|.
* sourceQPilotHullBound_iff:
    SourceQPilotHullBound (forall hull x, ld x <= |log q|)
      <-> sourceHullVolume <= ENNReal.ofReal |log q|.
* sourceQPilotHullBound_iff_comparison_and_finite:
    SourceQPilotHullBound <-> hfin and the signed comparison.
* sourceScaling_logDegree_nonpos_of_qPilotHullBound:
    under the q-scale bound, every s in sourceScalingUnits has ld s <= 0.
* sourceLocalLogDegree_add_le_qPilotMagnitude_of_qPilotHullBound:
    if the scaled-region bound C is attained at y in O and lam*y is in the hull,
    the q-scale bound forces ld(lam) + C <= |log q|.

## 3. Decisive negative result: unconditional collapse of the value hull

Proof idea.  sourceHolomorphicHull is a Submonoid of the value carrier and
sourceLocalLogDegree is additive.  If x in the hull has ld x > 0, then x^k is in
the hull and ld(x^k) = k * ld x, so the hull log-degree is unbounded and the hull
volume is top.  If no positive-degree hull point exists, every hull log-degree is
nonpositive and the hull volume is zero.  In both phases ENNReal.toReal top = 0
and toReal 0 = 0, so the real hull log-volume is zero.  No degree-faithfulness
premise is used.

Reused read-only phase dichotomy:

    CardHullRealFinitePhaseGate.sourceHullVolume_eq_top_iff_exists_pos_logDegree
    CardHullRealFinitePhaseGate.sourceHullVolume_lt_top_iff_forall_logDegree_nonpos
    CardHullRealEdgeNormalizationDichotomy.sourceHullVolume_eq_zero_of_hull_logDegree_nonpos

New theorems in the file:

* sourceRealHullVolume_eq_zero: sourceRealHullVolume v R n = 0 for every
  v, R, n (no hdeg, no q condition).
* sourceSignedHullLogVolume_eq_zero: sourceSignedHullLogVolume v R n = 0.
* sourceXifSignedComparisonAtQPilot_unconditional: the literal (xi-f)
  comparison holds for every source q.
* not_nonempty_sourceSignedQPilotCarrier: the non-collapsed carrier
  SourceSignedQPilotCarrier is empty for every realization.
* sourceQPilotHullBound_iff_hullVolume_eq_zero: the q-scale hull bound is
  equivalent to sourceHullVolume = 0, not to a positive finite bound.

Degenerate special cases, also proved:

* degree-faithful: the signed comparison holds while the finite q-scale bound
  fails (sourceXifSignedComparisonAtQPilot_degenerate_of_degreeFaithful).
* contracted hImage + hScaling: sourceRealHullVolume = 0,
  sourceSignedHullLogVolume = 0, the comparison holds, and the non-collapsed
  carrier is empty (sourceXifSignedComparisonAtQPilot_of_contractedGenerators,
  not_nonempty_sourceSignedQPilotCarrier_of_contractedGenerators).
* real volume zero: comparison holds for every q
  (sourceXifSignedComparisonAtQPilot_of_realVolume_eq_zero).
* real volume greater than |log q|: comparison fails
  (not_sourceXifSignedComparisonAtQPilot_of_realVolume_gt), so with a positive
  real volume the comparison would be genuine - but positivity is impossible.

## 4. Why the literal (xi-f) closes degenerately

The literal signed comparison is exactly

    sourceRealHullVolume <= |Real.log q|.

At the value realization sourceRealHullVolume is always 0, so the comparison is

    0 <= |Real.log q|,

i.e. qPilot <= 0.  This is true for every q and consumes no hull information.
The paper's WLOG branch -|log Theta| < 0 requires sourceRealHullVolume > 0,
which is provably impossible at this value layer
(sourceRealHullVolume_eq_zero).  Therefore:

* the current value hull cannot host the corpus comparison;
* the "discriminating power restored by the signed wrapper" exists only on
  abstract real data (sourceSignedSurface_comparison_not_forced_by_sign), not on
  any realized source carrier;
* the degree-faithful and contracted degeneracies recorded in the earlier files
  are special cases of the unconditional collapse.

## 5. Candidate signed carrier interface and exact hypotheses

SourceSignedQPilotCarrier fields:

1. q < 1 (the source q is contracted).
2. 0 < sourceRealHullVolume v R n (the paper's WLOG branch -|log Theta| < 0).
3. forall x in the hull, sourceLocalLogDegree v x <= |Real.log q|
   (the q-scale bound).

Proved:

* nonempty_sourceSignedQPilotCarrier_iff:
    Nonempty carrier <-> q < 1 and positivity and SourceQPilotHullBound.
* nonempty_sourceSignedQPilotCarrier_iff_comparison_and_positivity:
    given q < 1, Nonempty carrier <-> positivity and the signed comparison.
* If inhabited: signed hull < 0, qPilot < 0, comparison, hull finiteness,
  certificate and Cor312Conclusion
  (sourceSignedQPilotCertificate, sourceSignedQPilotCor312Conclusion).
* BUT not_nonempty_sourceSignedQPilotCarrier: no realization inhabits it.
  The conditional consumer theorem is valid but has an empty value-layer
  premise.  It must not be cited as a value-layer closure of the corpus
  comparison.

## 6. Ambient O-module route and its exact residual

Proved:

* sourceQPilotHullBound_of_scaledRegion:
    hull subset scaledRegionImage lam O, every y in O has ld y <= C, and
    ld(lam) + C <= |log q| imply the q-scale hull bound.
* sourceQPilotHullBound_of_oneCircUCompactness and
  sourceQPilotHullBound_of_unitRegionHaarData: the same with the containment and
  the bound C taken from SourceOneCircUCompactness / SourceUnitRegionHaarData.
* sourceLocalLogDegree_add_le_qPilotMagnitude_of_qPilotHullBound:
    if C is attained at y in O and lam*y lies in the hull, the q-scale bound
    forces ld(lam) + C <= |log q|.  So at a tight point the numeric
    normalization is exact, not an artifact of a sufficient direction.

But at the value layer SourceQPilotHullBound is equivalent to
sourceHullVolume = 0 (sourceQPilotHullBound_iff_hullVolume_eq_zero).  The
compactness data only gives finiteness, which is the zero value here.  The
numeric residual ld(lam) + C <= |log q| is therefore necessary at a tight point
but cannot repair the collapse of sourceHolomorphicHull.

## 7. Exact missing object / field (the answer)

The primary missing object is an ambient carrier for the holomorphic hull that
is NOT the least value-monoid submonoid, with a Haar log-volume on which a
bounded lambda.O region can have positive finite log-volume.  In paper terms:
IQ(S+-_{j+1}; n,circ D^vdash_{vQ}) with its ring-of-integers / O-module
structure and the normalized Haar log-volume.

What the tree currently has:

* sourceHolomorphicHull: a Submonoid of the value carrier.  Structurally its
  volume is 0 or top and its real part is 0.  This is the exact obstruction.
* SourceOneCircUCompactness / SourceUnitRegionHaarData: named data whose hull
  field is still sourceHolomorphicHull.  They give finiteness, but the value is
  0.
* IQHullLogVolumeInterface: an abstract interface; no realization for the
  actual IQ carrier.

The exact first missing field/lemma is therefore:

    a constructed ambient hull carrier H (not equal to sourceHolomorphicHull)
    with a log-volume mu, an O-module region O and a scaling lambda, the
    containment H subset lambda.O, and proofs
      0 < (mu H).toReal
      mu H <= ENNReal.ofReal |log q|
    (equivalently positivity plus the ambient q-scale bound).

Equivalently: a replacement hull H that is a bounded lambda.O region rather than
the least scaling-stable submonoid.  No numeric inequality alone can repair the
submonoid collapse of sourceHolomorphicHull.

If the project instead wants the value-layer numeric residual, the exact
sufficient condition (and necessary at a tight hull point) is

    sourceLocalLogDegree lam + C <= |log q|,

but it is not sufficient for positivity, which is impossible at
sourceHolomorphicHull.

## 8. Acceptance evidence

Command run from D:/lean:

    lake env lean -o tmp/sheaf/xif/paper/S2981SignedQPilotActual.olean tmp/sheaf/xif/paper/S2981SignedQPilotActual.lean

EXIT: 0
Source: 935 lines, 48700 bytes
Source SHA256: 7A1F25419C3DEEF289B983EB0DEA8D555B65FB65A9507DC120B46980FE19ECC4
Olean: 420680 bytes
Olean SHA256: 416C1AF58D1359D7EE308EAC06193CA130F8E5C6435F27197F0483A96CA41E7D

#print axioms: all 18 listed declarations depend on exactly
[propext, Classical.choice, Quot.sound].  The printed list:

    sourceQPilotSignedLog_eq_neg_abs_logDegree
    sourceXifSignedComparisonAtQPilot_iff_realPart_le
    sourceXifSignedComparisonAtQPilot_iff_hullVolume_le
    sourceXifSignedComparisonAtQPilot_degenerate_of_degreeFaithful
    sourceQPilotHullBound_iff
    sourceQPilotHullBound_iff_comparison_and_finite
    nonempty_sourceSignedQPilotCarrier_iff_comparison_and_positivity
    not_nonempty_sourceSignedQPilotCarrier_of_degreeFaithful
    not_nonempty_sourceSignedQPilotCarrier_of_contractedGenerators
    sourceLocalLogDegree_pow_mul
    sourceScaling_logDegree_nonpos_of_qPilotHullBound
    sourceQPilotHullBound_of_scaledRegion
    sourceRealHullVolume_eq_zero
    sourceSignedHullLogVolume_eq_zero
    sourceXifSignedComparisonAtQPilot_unconditional
    not_nonempty_sourceSignedQPilotCarrier
    sourceQPilotHullBound_iff_hullVolume_eq_zero
    sourceSignedQPilotCor312Conclusion

Forbidden-token check: no sorry, admit, axiom declaration, placeholder, True,
opaque, unsafe, or native_decide.  The words sorry / axiom / placeholder / True
appear only in comments and in the #print axioms commands.
No existing source file was modified.  Only the new Lean file and this report
were written.

## 9. Key declaration map

Line numbers in tmp/sheaf/xif/paper/S2981SignedQPilotActual.lean:

    143  sourceThetaPacketQ
    149  sourceQPilotLogMagnitude
    154  sourceQPilotSignedLog
    196  sourceQPilotSignedLog_eq_neg_abs_logDegree
    206  sourceQPilotSignedLog_neg_iff
    229  SourceXifSignedComparisonAtQPilot
    246  sourceXifSignedComparisonAtQPilot_iff_realPart_le
    256  sourceXifSignedComparisonAtQPilot_iff_hullVolume_le
    307  sourceXifSignedComparisonAtQPilot_degenerate_of_degreeFaithful
    322  SourceQPilotHullBound
    331  sourceQPilotHullBound_iff
    350  sourceQPilotHullBound_iff_comparison_and_finite
    384  sourceScaling_logDegree_nonpos_of_qPilotHullBound
    432  SourceSignedQPilotCarrier
    467  sourceSignedQPilotCarrier_comparison
    504  nonempty_sourceSignedQPilotCarrier_iff_comparison_and_positivity
    523  not_nonempty_sourceSignedQPilotCarrier_of_degreeFaithful
    591  not_nonempty_sourceSignedQPilotCarrier_of_contractedGenerators
    609  sourceQPilotHullBound_of_scaledRegion
    628  sourceLocalLogDegree_add_le_qPilotMagnitude_of_qPilotHullBound
    655  sourceQPilotHullBound_of_oneCircUCompactness
    725  sourceSignedQPilotCertificate
    760  sourceSignedQPilotCor312Conclusion
    787  sourceRealHullVolume_eq_zero
    805  sourceSignedHullLogVolume_eq_zero
    815  sourceXifSignedComparisonAtQPilot_unconditional
    826  not_nonempty_sourceSignedQPilotCarrier
    838  sourceQPilotHullBound_iff_hullVolume_eq_zero
    876  cardHullRealSignedQPilotActual (audit obligation)

## 10. Next executable step

1. Construct or name an ambient hull carrier that is not sourceHolomorphicHull.
   The immediate formal target is a structure with:
   - carrier X and logVolume : Set X -> ENNReal;
   - hull : Set X, imageSet subset hull, hull subset scaledRegionImage lam O;
   - O-degree bound C and the numeric normalization ld(lam) + C <= |log q|;
   - 0 < (logVolume hull).toReal and logVolume hull <= ofReal |log q|.
   The existing IQCarrierHaarData / OModuleCompactnessLayer interfaces can be
   reused for the log-volume field, but their hull must NOT be instantiated with
   sourceHolomorphicHull, because that instantiation is refuted by
   sourceRealHullVolume_eq_zero.
2. Prove the tight-point normalization on the ambient carrier.  If the carrier
   is still a value monoid with an O-region, port the template
   sourceLocalLogDegree_add_le_qPilotMagnitude_of_qPilotHullBound; otherwise
   translate the argument to the ambient degree.
3. Instantiate the certificate and Cor312Conclusion at the ambient hull.
   Only then claim the non-collapsed signed comparison.
4. Do not add a hypothesis 0 < sourceRealHullVolume anywhere: it is refuted
   unconditionally.  Any future file assuming it is inconsistent.

## 11. Caveats

* The q-pilot used here is the source theta-packet quantity -|log q|.  The
  arithmetic finite-place q-family quantity is a different actual object; its
  identification with the source q is a separate missing bridge.
* The unconditional collapse is a theorem about the tree's value realization.
  It does not say the paper's Corollary 3.12 is false; it says the current
  value-monoid hull cannot host the non-collapsed signed comparison.
* The paper's O-module carrier, the compactness of 1,circ U, and any
  non-value-realized positive finite hull are NOT constructed here.
* The conditional consumer theorem sourceSignedQPilotCor312Conclusion is a
  valid assembly but has an empty value-layer premise; it must not be cited as
  a value-layer closure.
