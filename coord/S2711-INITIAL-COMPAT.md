# S2711-INITIAL-COMPAT — is S2711's initial definitionally S1487FaithfulSourceData?

Status: READ-ONLY audit, 2026-11-12. No compile.
Objects:
- S2711HcompMultiActual.lean:32 / S2711PaperMultiUnconditionalActual.lean:226-234
- S2706DirectHcompActual.lean:27-63
- S2717Cor312FullTargetActual.lean:50-76
- S1487OQPilotScalarEqualityActual.lean:394-550
- Mzk1S1487SourceRootIdentityActual.lean:48-54
- Mzk1S1487QPilotTargetActual.lean:65

## 1. Exact definitions

S2711I (S2711PaperMultiUnconditional:226-234) is an abbrev for
  S2706I R redCompat ... cusCompat.
S2706I (S2706DirectHcomp:41-51) is
  S1487OriginalInput
    (S2706SourceData R redCompat ... cusCompat).
S2706I_initial (S2706:53-63) is rfl:
  (S2706I ...).initial =
    S2706SourceData R redCompat ... cusCompat.
Therefore
  (S2711I ...).initial = S2706SourceData ...   [rfl, after unfolding S2711I].

S1487RootInput (Mzk1S1487SourceRootIdentity:48-51) is
  S1487OriginalInput (S1487FaithfulSourceData l).
S1487RootInput_initial (Mzk1S1487SourceRootIdentity:53-54) is rfl:
  (S1487RootInput l).initial = S1487FaithfulSourceData l.

So the two sides are both rfl-reduced, but to DIFFERENT source data:
  left  = S2706SourceData ...
  right = S1487FaithfulSourceData l.

## 2. Are the two source data definitionally equal?

S2706SourceData (S2704S2696SourceData:150-162) is
  Definition31PlacePartition.d11EntryData
    (P := S2696SelectionTwo l)
    (C := S2696ReductionCards l)
    R.torsion R.orbicurve R.sections R.cusp
    redCompat hredCompat ... cusCompat hcusCompat.
Its arithmetic is S1280Arithmetic l = concreteGaussianInitialThetaArithmeticData l
(S2704:164-175), and its bad-place type is Bad (S2696SelectionTwo l)
(S2704:177-188). S2696SelectionTwo has the two concrete bad places 5 and 2161
(S2696BadFive, S2696Bad2161); the q parameter is the completed-DVR proxy
badPlaceQProxy, and sourceBadQAbsLog is the sum over those two places.

S1487FaithfulSourceData (S1487:520-524) is
  S1487SourceData (l := l) PUnit (fun _ => ||S1487Cand.q||)
    ...,
where S1487SourceData (S1487:400-501) sets:
  arithmetic := S1487Arithmetic l = concreteGaussianInitialThetaArithmeticData l;
  selectedPlaces := Unit;
  badPlaces := PUnit;
  reduction.qParameter := the constant ||S1487Cand.q||;
  torsion/orbicurve/sections/cusp := the fixed concrete placeholders of S1487
    (ZMod 6 torsor, Unit orbicurve, Unit sections, epsilon/cusp data), not
    R.torsion/R.orbicurve/R.sections/R.cusp.
Thus even the arithmetic fields are definitionally the same concrete Gaussian
arithmetic, but the SourceDefinition31Data values are not definitionally equal:
- bad-place types/cardinalities differ: Bad (S2696SelectionTwo l) vs PUnit;
- selected places differ: S2696SelectionTwo's V_mod vs Unit;
- reduction q parameters differ: badPlaceQProxy at 5 and 2161 vs constant
  ||S1487Cand.q|| at PUnit;
- the four remaining clauses differ: R.torsion etc from S1280RemainingClauses vs
  S1487's fixed concrete clauses;
- the five compatibility Props/proofs differ.

Hence there is no rfl or congrArg proof of
  S2706SourceData ... = S1487FaithfulSourceData l.
S2711InitialCompatibility is therefore NOT definitionally true. It is an
equality between different concrete source data, not a definitional unfolding.

## 3. Is it provable at all?

An equality of SourceDefinition31Data records would require, among other things,
an equality/transport of the bad-place index types. The S2696 selection has two
bad places (5 and 2161); S1487FaithfulSourceData has one (PUnit). There is no
equality between these index types, and no theorem collapsing the two S2696
places to one. The reduction q values also differ (proxy at two places vs the
single actual Gaussian q magnitude). Therefore the full data equality is not
merely missing: it is incompatible with the current concrete definitions.

What can still be compared is the scalar q-pilot volume, without equating the
whole source data:
  sourceQPilotSignedLog (S2711I ...).initial
    = -sourceBadQAbsLog (S2706SourceData ...)       [rfl/definition]
  S1487SignedLogVolume l
    = -OrigXiFPaperBadQAbsLog (S1487FaithfulSourceData l)  [proved in
      Mzk1S1487QPilotTargetActual]
The honest bridge is a scalar equality
  sourceBadQAbsLog (S2706SourceData ...)
    = OrigXiFPaperBadQAbsLog (S1487FaithfulSourceData l),
not an equality of initials. That scalar equality is also a GAP/extra
hypothesis: S2696 has a two-place bad sum, S1487 has a one-place magnitude.

## 4. Minimal identification conditions

If one insists on an initial equality, the minimal data are:
1. A concrete source datum S (or a proof S2706SourceData = S1487FaithfulSourceData)
   including equality of bad-place types/values and reduction q parameters.
2. Equality of the four clause fields and five compatibility fields.
3. Equality of arithmetic fields (definitionally true here, but needed in the
   transported record).
This is not available and is incompatible with the two-place vs one-place
selection. Do not add it as an assumption for S2717; it would be a fake
identification.

The useful weaker conditions are:
A. Scalar volume compatibility:
   sourceBadQAbsLog (S2706SourceData ...) =
     OrigXiFPaperBadQAbsLog (S1487FaithfulSourceData l).
   This suffices for the signed scalar comparison and does not assert source
   data equality.
B. Or a separate concrete q-parameter/logQ selection for S2711 that is proved
   to equal the S1487 canonical one. The S1487 canonical logQ is
   2l * OrigXiFPaperBadQAbsLog S1487FaithfulSourceData (S1487CanonicalLogQ);
   S2711's q data must be separately related to it.

## 5. Lean templates

rfl reductions (both true as stated):
  theorem S2706I_initial ... :
      (S2706I ...).initial = S2706SourceData ... := rfl
  theorem S1487RootInput_initial (l) :
      (S1487RootInput l).initial = S1487FaithfulSourceData l := rfl
  theorem S2711I_initial ... :
      (S2711I ...).initial = S2706SourceData ... := rfl

No template for
  S2706SourceData ... = S1487FaithfulSourceData l
is given: it is false/incompatible with the current data, not merely unproved.

A conditional scalar bridge:
  theorem S2711_signedVolume_eq_S1487
      (h : sourceBadQAbsLog (S2706SourceData ...) =
        OrigXiFPaperBadQAbsLog (S1487FaithfulSourceData l)) :
      sourceQPilotSignedLog (S2711I ...).initial =
        S1487SignedLogVolume l := by
    rw [S2706I_initial?, sourceQPilotSignedLog_eq_neg_badQAbsLog,
      S1487SignedLogVolume, S1487RootInput_initial,
      sourceQPilotSignedLog_eq_neg_badQAbsLog, h]
This is a conditional scalar bridge; it does not prove the initial equality.

## 6. Verdict

- S2711I is definitionally S2706I; its initial is rfl S2706SourceData.
- S1487RootInput's initial is rfl S1487FaithfulSourceData.
- The two source data are NOT definitionally equal, and not equal under current
  concrete definitions: two bad places vs PUnit, different q parameters, different
  clauses.
- GAP-S2711-INITIAL is real and should not be closed by an equality axiom.
  Replace it by a scalar bad-q-volume compatibility (explicit hypothesis/data),
  or by a separately constructed common source datum.
- No Lean file written; no compile claimed.
