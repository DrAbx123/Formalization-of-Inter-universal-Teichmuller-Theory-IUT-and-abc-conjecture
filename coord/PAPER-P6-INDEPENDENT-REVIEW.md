# Independent review: PaperP6FullTarget source semantics

Date: 2026-10-25
Reviewer: transport
Mode: read-only semantic review. No Lean edits, no proof changes.

## Reviewed objects

| file | lines | SHA256 |
|---|---:|---|
| tmp/sheaf/n8/closure/PaperP6FullTarget.lean | 52 | D79DAAAF389EA3D3BECF72D0E901E5E249F95DAA3A9CBEE0575986DBBD16ED49 |
| tmp/sheaf/n8/closure/PaperP6Target.lean | 32 | D9981A009EF5398C4AE303AE29CCA807E927F8033BC30E8AEC9D7925B32D59AE |
| tmp/sheaf/n8/closure/PaperValuesBoundedActual.lean | 81 | D507DD22BCBA45B4CC88F490B2AF8775C048B4FF22121117051C06CD84397CA1 |
| tmp/sheaf/n8/closure/PaperP6Final.lean | 84 | 2F2B8884E72E25CDC9758E6D0762CAE3293C954520109448F8FA6E24838D9088 |

Target:

    def PaperP6FullTarget (S : SourceInitialThetaData l) : Prop :=
      PaperP6Target S ∧ PaperValuesBoundedTarget S

    PaperP6Target S :=
      ∃ qLog thetaLog : Real,
        qLog = Real.log ‖(qUnit S : PaperKf S)‖ ∧
        thetaLog = thetaLogVolume S ∧
        qLog <= thetaLog ∧
        (thetaLog : WithTop Real) < top

    PaperValuesBoundedTarget S :=
      ∀ T : Set (Block S),
        T ⊆ c6Hull ... ->
        Real.log ((c6UnitRefNormalizedData ... T).toReal) <=
          thetaLogVolume S

## Verdict

source_semantics_review = PARTIAL

The Q and Theta numeric objects are actual:
- qUnit comes from ClauseB qParameter at the chosen lifted bad place;
- thetaLogVolume is the logarithm of the actual C6 unit-reference normalized
  canonical hull.

The values part is not yet paper-source faithful:
PaperValuesBoundedTarget quantifies over EVERY subset T of the actual C6 hull,
not over the actual paper ValuesPaper provenance/source-output regions.  This is
stronger than the paper's value bound and does not connect to the paper values
provenance.  It is not an arbitrary inequality, and it is not circular, but it
is a different proposition from "all paper values are bounded by Theta".

## (1) Q: actual q or arbitrary Real?

Status: ACTUAL, with a locality qualification.

Chain:
- C7QPilotRegionActual.p0 chooses S.clauseB.bad_nonempty.
- pF is an actual lift of p0 to a finite F-place via comap_surjective.
- qCandidate = S.clauseB.qParameter pF pF_bad.
- q = qCandidate.q, qAtPrime = q.
- qUnit = Units.mk0 qAtPrime (q_ne_zero).
- PaperP6Target pins qLog by qLog = Real.log ‖qUnit‖.

Therefore qLog is the log norm of the actual ClauseB q parameter, not an
arbitrary Real.  PaperP6Target's existential qLog is also not arbitrary: both
existential witnesses are pinned by equalities to qUnit and thetaLogVolume.

Qualification: this is the q parameter at one chosen bad place and on the
one-factor C6 block.  It is not the full product of q parameters over all bad
places.  That is a locality restriction, not an arbitrary Real.

## (2) Theta: actual C6 unit-reference normalized canonical hull?

Status: ACTUAL for the C6 canonical hull.

Chain:
- thetaLogVolume = Real.log (normalized mass of c6Hull).toReal.
- c6Hull is the C6 IQ interface hull.
- PaperP6ComparisonActual.c6Hull_eq_canonicalHull proves it equals
  arithmeticTupleCanonicalHull.
- The measure is c6UnitRefNormalizedData, i.e. normalized by the actual
  arithmeticTupleCanonicalUnitReference mass, with unit-reference mass 1.
- theta finite is proved in PaperP6Final.thetaMass_lt_top from the actual
  canonical-regions finite-mass theorem.

So Theta is the actual normalized canonical C6 hull, not an arbitrary real.
Qualification: it is the one-factor C6 canonical hull, not the C9Paper
ThetaPaper provenance with its thetaToC6 donor.  The C9 bridge gap is separate.

## (3) ValuesBounded: only inside the actual Theta hull?

Status: PARTIAL.

What is good:
- The hypothesis is T ⊆ c6Hull, so no set outside the actual Theta hull is
  admitted.
- The inequality uses the actual normalized C6 measure and the actual Theta
  log-volume; it is not a free Real inequality.
- The proof handles T with mass 0 and top separately, and uses monotonicity on
  the actual hull.

What is not paper-faithful:
- T ranges over ALL subsets of the hull, including sets that are not actual
  paper values/source regions.  Paper P6 concerns the actual ValuesPaper
  provenance (C6ImageSet / normalizedLogVolume on source output sets), not an
  arbitrary subset T.
- There is no use of ValuesPaper, SourceWitnessedOutputData, or the actual
  source-output region in PaperValuesBoundedTarget.
- Consequently the theorem is stronger set-theoretically but weaker
  source-semantically: it does not state that the paper values are bounded,
  only that every subset of the hull is bounded.

Verdict for this field: partial, not invalid.  It is not an arbitrary
inequality, but it does not yet encode the paper values provenance.

## (4) Circularity / target assumption / hidden arbitrary

- No circularity found:
  PaperP6FullTarget imports PaperP6Target and PaperValuesBoundedActual.
  PaperValuesBoundedActual uses thetaLogVolume_nonneg from
  PaperP6ComparisonActual, not PaperP6FullTarget.
  No theorem in the reviewed chain assumes PaperP6FullTarget.
- No target assumption:
  PaperP6Target constructs its witnesses from actual qUnit/thetaLogVolume.
  PaperValuesBoundedTarget is proved from actual hull containment and measure
  monotonicity.
- No arbitrary inequality:
  the only inequality is measure_mono plus Real.log_le_log on actual masses;
  the q/theta values are pinned by equalities.
- Hidden quantification issue:
  the unrestricted T quantification in PaperValuesBoundedTarget is the main
  semantic overreach, but it is not an arbitrary data witness.  It is a
  universal statement over sets, not the paper's ValuesPaper set.
- One source-level caveat: PaperP6Target's existential qLog/thetaLog are
  variables, but their equalities remove freedom.  This is acceptable.

## Required source-level gaps

1. Values provenance bridge.  Replace/augment PaperValuesBoundedTarget with a
   statement over the actual ValuesPaper provenance (or actual C6ImageSet/
   source-output region), e.g.:

       forall z ∈ ValuesPaper.values, z <= thetaLogVolume

   This requires an actual construction of ValuesPaper provenance from
   SourceInitialThetaData/SourceWitnessedOutputData, which is not present in the
   reviewed files.

2. C9Paper provenance bridge.  QPaper.qPilotLogVolume = localSignedLog C3.q
   and ThetaPaper.thetaLogVolume = C6.normalizedLogVolume (thetaToC6 thetaHull)
   are not proved equal to PaperP6's qUnit log and thetaLogVolume.  The exact
   volume-level bridge is recorded in PaperP6ToC9.C9VolumeBridge /
   C9BridgeGap; no production provenance construction exists.

3. Locality qualification.  Both Q and Theta are one-factor/C6-canonical
   quantities.  The paper's Q/Theta may require the full bad-place product and
   the actual theta image; the reviewed target does not claim that.

## Final assessment

- Q actual ClauseB q parameter: YES (at chosen bad place, one-factor block).
- Theta actual C6 normalized canonical hull: YES (C6 canonical, one-factor).
- ValuesBounded only over actual Theta-hull regions: PARTIAL.  It is bounded by
  the actual hull but quantified over arbitrary subsets, not actual paper
  values.
- Circular/target-assumed/hidden arbitrary: NO (no circularity, no arbitrary
  Real; unrestricted T is the semantic issue).

source_semantics_review = PARTIAL.

The target is a valid actual C6/one-factor P6 assembly, but it is not yet a
complete paper-source P6 statement: the ValuesPaper provenance and the
C9Paper provenance bridge remain exact gaps.


## Correction 2026-10-25 (Lead)

`PaperP6ToC9.C9BridgeGap` as originally defined is FALSE, not a gap:
`C9VolumeBridge` only requires qVolume/thetaVolume equalities to the paper
log-volumes, which are trivially satisfiable. `c9BridgeGap_false` now proves
`¬ C9BridgeGap`.

The real remaining provenance gap is C9Paper's own `QPaper.qPilotLogVolume`
and `ThetaPaper.thetaLogVolume` equalities (and `C3.q` matching), not existence
of a volume record. This correction does not change the target verdict
(PARTIAL) or target_accepted=false.
