# VOLUME-IDENTIFICATION — theta/q-pilot volume candidates and the missing common-mu bridge

Status: READ-ONLY, 2026-11-12. No compile. Related fix: Mzk1CThetaRetargetActual.lean
L88 rewrite corrected (rw [habs]); reported to mainline; file awaits watchdog.

## 1. Theta side: already on the actual Haar measure

S2717ThetaHullLogVolume (S2717Cor312FullTargetActual.lean:50-67):
  - (globalThetaHullInterface.logVolume (globalThetaHull)).toReal.
S2807_thetaHullVolume_eq_haarRegion (S2807ThetaHullVolumeIdentityActual.lean:40-47):
  S2717ThetaHullLogVolume = - (haarLogVolume
    (actualC3LogShellTensorHaar C3) (actualC3LogShellTensorRegion C3)).toReal.
Also S2807_paperCor312Full_iff_haarRegion rewrites PaperCor312Full to the same
actual Haar region (plus the CThetaPaper upper and -1<=CThetaPaper).

So the theta side has a clean common-mu representation:
  thetaLogVolume = negHaarLog mu thetaRegion,
  mu = actualC3LogShellTensorHaar C3,
  thetaRegion = actualC3LogShellTensorRegion C3.

## 2. Q side candidates: all scalars, none currently on mu

(1) S2717QPilotLogVolume (S2717Cor312FullTargetActual.lean:69-76):
    = sourceQPilotSignedLog (S2711I ...).initial.
    It is a source scalar, not a Haar integral over a C3 region.
(2) HullDetObjectActual.qPilotLogVolume (HullDetObjectActual.lean:158-165):
    = qPilotLogVolumeReading P = -|Real.log (‖P.line.C3.q.q‖)|.
    Also a scalar q reading; no Haar measure.
(3) S3016StepVQPilot (S3016StepVQPilotIdentificationActual.lean:30):
    = S2736QPilotLineBundleLogVolume (S2752J ... a b c).
    A StepV line-bundle log volume; not a C3 Haar log-volume.
(4) S3016WeightedGlobalQPilot / nativeGlobalQPilotNormalizedLogMagnitude:
    weighted native scalar; not a C3 Haar integral.

No declaration in these files constructs a set qPilotRegion in the C3 tensor
block and proves that its actual Haar log-volume equals any of the q-side
scalars. The exact missing object is therefore the identification with the
common mu, not another arithmetic rewriting.

## 3. Sign convention and the correct subset direction

Both S2717ThetaHullLogVolume and the desired qPilotLogVolume are negative
quantities of the form -|log(...)|, and S2807 represents theta as
  thetaLogVolume = - (haarLogVolume mu thetaRegion).toReal.
Suppose qPilotLogVolume is represented the same way:
  qLogVolume = - (haarLogVolume mu qPilotRegion).toReal.
To prove qLogVolume <= thetaLogVolume (the paper direction -|log q| <= -|log Theta|),
we need:
  -(haarLogVolume mu qRegion) <= -(haarLogVolume mu thetaRegion)
  <=> haarLogVolume mu thetaRegion <= haarLogVolume mu qRegion.
By monotonicity of Haar log-volume, this follows from
  thetaRegion ⊆ qPilotRegion,
i.e. theta ⊆ q, NOT q ⊆ theta. If one only has qRegion ⊆ thetaRegion, monotonicity
gives the opposite inequality.

This is a critical orientation: with the negHaarLog normalization used by S2717,
the sufficient geometric inclusion is thetaHullRegion ⊆ qPilotRegion. The earlier
CTHETA-RETARGET-IMPL subgoal B phrased qPilotRegion ⊆ thetaHullRegion under a
log-mu signed convention; for the negHaarLog convention of S2717 the direction
must be reversed. Any theorem to be consumed by S2717 must use theta ⊆ q.

## 4. Proposed minimal bridge declarations

The following are the minimal new declarations; none exist in the audited tree.

1. qPilotHaarRegion:
     noncomputable def qPilotHaarRegion
       (C3 : SourcePilotRegionData ...) : Set (C3LogShellTensorBlock C3).
   Candidate: a q-pilot line/tensor region built at (1,0) from the same C3
   block, or an existing HullDet literalIQHull/globalIQUnitRegion if it can be
   identified with the q-pilot scalar.

2. qPilotLogVolume_eq_neg_haarLog:
     S2717QPilotLogVolume ... =
       - (haarLogVolume (actualC3LogShellTensorHaar C3) (qPilotHaarRegion C3)).toReal
   (with finite-measure side condition). This is the missing equality.

3. thetaRegion_subset_qPilotRegion:
     actualC3LogShellTensorRegion C3 ⊆ qPilotHaarRegion C3.
   This is the geometric theta⊆q inclusion, not q⊆theta.

4. negHaarLogVolume_mono (or a direct derivation):
     from thetaRegion⊆qRegion and measure finiteness,
     - (haarLogVolume mu qRegion).toReal <= - (haarLogVolume mu thetaRegion).toReal.

5. Assemble:
     S2717QPilotLogVolume <= S2717ThetaHullLogVolume
   by 2, S2807_thetaHullVolume_eq_haarRegion, 3, 4.

No new generic monotonicity is needed: haarLogVolume_mono already exists
(FinitePlaceIQHullInterface.lean:68); only the q-region/scalar identification and
the theta⊆q inclusion are missing.

## 5. Existing assets that can be reused

- S2807_thetaHullVolume_eq_haarRegion: exact theta side on actual mu.
- S2807_paperCor312Full_iff_haarRegion: full target rewritten on the same mu.
- haarLogVolume_mono (olean present): measure monotonicity.
- QRegionCarrierInterface.logVolume_mono: interface-level monotonicity.
- HullDetObjectActual.literalIQHull / literalIQHullLogVolume:
  actual global IQ hull Haar readout; candidate q-side region, but no theorem
  identifies it with S2717QPilotLogVolume or HullDet qPilotLogVolume.
- Mzk1SignedLogVolumeCor312Actual.XiEContainment/signedLogVolume:
  compatible with log-measure signed convention, NOT with -haarLog; use only if
  the region scalar is re-expressed as log mu. For S2717's negHaarLog convention
  use haarLogVolume_mono plus negation.

## 6. Exact GAP statement

There is no theorem of the form
  S2717QPilotLogVolume ... =
    - (haarLogVolume (actualC3LogShellTensorHaar C3) qPilotRegion).toReal
and no theorem
  actualC3LogShellTensorRegion C3 ⊆ qPilotRegion.
The q-side candidates are source scalars/StepV line-bundle volumes/HullDet scalar
readings, not C3 Haar integrals. Therefore the paper inequality
S2717QPilotLogVolume <= S2717ThetaHullLogVolume is not yet derived from the
common-mu representation, even though the theta side is exact.

## 7. Direction verdict

- Theta side: exact common-mu representation exists (S2807).
- Q side: no common-mu region/equality exists; all candidates are scalars.
- Correct sufficient geometric inclusion for the negHaarLog used by S2717 is
  thetaHullRegion ⊆ qPilotRegion (theta⊆q).
- The earlier q⊆theta phrasing is valid only for a log-measure signed convention
  without the outer negation; it is the wrong direction for S2717's -haarLog.
- Do not claim qPilot⊆theta from S2717; that would produce the opposite
  inequality under -haarLog.

No Lean file written; no compile claimed.
