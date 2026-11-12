# Independent review: PaperP6ValuesTarget source semantics

Date: 2026-10-25
Reviewer: transport
Mode: read-only semantic review. No Lean edits, no proof changes.

## Reviewed artifacts

| file | lines | SHA256 |
|---|---:|---|
| tmp/sheaf/n8/closure/PaperP6ValuesTarget.lean | 30 | F04D1FEBBC03CB5BE9E04742C942C4F86A87E2237A10E674C64D9BD0C23022E5 |
| tmp/sheaf/n8/closure/PaperValuesFamilyActual.lean | 52 | C72467D69195D89AE26C9F400EE37420A7BEC2CFA0356121A436C555BDFF658F |
| tmp/sheaf/n8/closure/PaperAllQPilotRegions.lean | 88 | 7D175248C69B829D3BD5C3F2907BC4941969741414F99F925557180CAEDBA778 |
| coord/targets/ChallengeValues.lean | 15 | 5592002F0906346216ABD32AAEA225DEF8BF8CD2ED98A3EB27FDF74220D47302 |
| coord/targets/TargetsCheckValues.lean | 19 | 3B1A1B5F932235286143EE87611FB93BBC051107F63FB7CF8C009A9BED75C58A |

Target:

    PaperP6ValuesTarget S :=
      PaperP6Target S ∧
        forall z in paperValueSet S, z <= thetaLogVolume S

    paperValueSet S :=
      { z | exists T in allQPilotRegions S,
              z = Real.log
                ((c6UnitRefNormalizedData (places S) (tuple S) T).toReal) }

    allQPilotRegions S :=
      { T | exists q : (PaperKf S)^x,
              ||(q : PaperKf S)|| <= 1 ∧
              T = qPilotRegionOf S q }

    qPilotRegionOf S q :=
      e.symm '' (q * Integers(PaperKf S))

## Verdict

source_semantics_review = PARTIAL

PaperP6ValuesTarget is a genuine improvement over the hull-universal
PaperValuesBoundedTarget:
- values are restricted to actual q-pilot regions q * Integers, not arbitrary
  subsets of the hull;
- q ranges over actual units of the paper completion satisfying norm <= 1;
- qPilotRegionOf is constructed from the actual e and actual Integers;
- Q and Theta are the same actual objects as in PaperP6Target.

It is still not the full paper Values statement:
- paperValueSet is the set of ALL norm<=1 q-pilot normalized log-volumes,
  not the actual paper ValuesPaper provenance/source output family;
- it does not use C9Paper.ValuesPaper, SourceWitnessedOutputData, or the
  actual possible-theta image set;
- no C9 / ValuesPaper provenance bridge is constructed.

## (1) paperValueSet actual construction from allQPilotRegions?

Status: ACTUAL for the stated q-pilot family.

- qPilotRegionOf q = e.symm '' (q * Integers) is an actual set on the actual
  one-factor C6 block.
- allQPilotRegions contains exactly those sets for units q with
  ||q|| <= 1.  The condition is the actual completion norm, not an arbitrary
  predicate.
- paperValueSet takes the actual normalized C6 measure
  c6UnitRefNormalizedData and computes Real.log of the finite mass toReal.
- paperValueSet is nonempty: qUnit is norm<1 and qPilotRegion is included.

No arbitrary Real or arbitrary set of reals is introduced.  The witness q is an
actual unit of CommonPrimeCompletion (placeAtPrime S).

## (2) Q/Theta actual?

Status: ACTUAL (same as the prior P6 review).

PaperP6ValuesTarget uses PaperP6Target:
- Q.qLog = Real.log ||qUnit||, with qUnit from ClauseB qParameter at the chosen
  lifted bad place; actual.
- Theta.thetaLog = thetaLogVolume, the log of the actual C6 unit-reference
  normalized canonical hull; actual, finite.
- qLog <= thetaLog is the actual PaperP6ComparisonActual theorem.

Neither Q nor Theta is a free Real; both are pinned by equalities.

## (3) Is Values closer to paper Values than hull-universal?

Status: CLOSER, but still PARTIAL.

Improvement over PaperValuesBoundedTarget:
- the old target quantified over every T subset c6Hull;
- the new target quantifies only over T in allQPilotRegions, i.e. actual
  q*Integers images for q with norm <= 1.

Remaining difference:
- the paper Values (C9Paper.ValuesPaper) are the actual C6 normalized
  log-volumes of a provenance set; the provenance is not constructed here.
- the new paperValueSet is a q-pilot family indexed by all norm<=1 units; it
  need not coincide with the paper's finite/source-constrained value family.
- allQPilotRegions includes many q values not selected by the paper's
  C1/C2/C3/source-output provenance.

So this is a mathematically actual q-pilot value family, but not yet the paper
ValuesPaper family.

## (4) Circularity / target assumption / hidden arbitrary

- No circularity:
  PaperP6ValuesTarget imports PaperValuesFamilyActual and PaperP6Target.
  PaperValuesFamilyActual uses PaperAllQPilotRegions and actual C6 measure;
  none assumes PaperP6ValuesTarget.
  ChallengeValues/TargetsCheckValues import the target only as a frozen
  statement and prove it via paperP6ValuesTarget_actual.
- No target assumption:
  paperP6ValuesTarget_actual is proved by pairing actual PaperP6Target and
  actual paperValueSet_bounded.
- No arbitrary Real:
  q is an actual unit, norm condition is actual, T is actual q*Integers, mass
  is actual normalized C6 measure.
- Hidden quantifier issue:
  paperValueSet ranges over all q with ||q||<=1, which is broader than the
  paper's ValuesPaper provenance.  That is the remaining semantic gap, not an
  arbitrary witness.
- Frozen snapshots ChallengeValues and TargetsCheckValues are consistent with
  PaperP6ValuesTarget; the check theorem has no sorry in the reviewed source.

## Remaining C9 provenance gaps

1. ValuesPaper provenance:
   no construction of ValuesPaper (or its C6 provenance set) from
   SourceInitialThetaData / SourceWitnessedOutputData; paperValueSet is a
   q-pilot family, not the paper values family.

2. QPaper provenance:
   C9Paper.QPaper.qPilotLogVolume = localSignedLog C3.q is not proved equal to
   PaperP6's log||qUnit||.  C3.q and qUnit are different source paths.

3. ThetaPaper provenance:
   C9Paper.ThetaPaper.thetaLogVolume =
   C6.normalizedLogVolume (thetaToC6 thetaHull); no production thetaToC6 donor
   nor equality to PaperP6's thetaLogVolume.

4. Locality:
   Q/Theta and paperValueSet live on the one-factor C6 block at the chosen bad
   place; the full paper product / actual theta image is not constructed.

## Final assessment

- paperValueSet actual from allQPilotRegions: YES, for the q-pilot family.
- Q actual ClauseB q parameter: YES.
- Theta actual C6 unit-reference normalized canonical hull: YES.
- Values closer to paper Values than hull-universal: YES, but still PARTIAL.
- C9 provenance bridge: NOT constructed.
- Circularity/target assumption/arbitrary Real: NO.

source_semantics_review = PARTIAL.

The target is a valid actual q-pilot-values P6 assembly and a real improvement
over the hull-universal version, but it is not yet the paper ValuesPaper/C9
statement.
