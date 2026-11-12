# CTHETA-RETARGET-IMPL — implementation plan and D19-D24 direction check

Status: FILE WRITTEN, NOT COMPILED. Lean source:
tmp/sheaf/xif/paper/Mzk1CThetaRetargetActual.lean. Hand to watchdog.
No compile run.

## 1. Lean file: declarations

File imports S2691, S2715, S2714 and Mathlib.Tactic; namespace
LeanFormal.IUT.XiFPaper.Mzk1CThetaRetargetActual.

### CThetaPaper_mul_A_le_CTheta_mul_A
For l : PrimeGeFive, parameters logQ dmod dFpd fFpd eStar etaPrm : Real,
with
  hA : 1 ≤ paperQAbsLog l logQ
  hB : 0 ≤ cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm
conclude
  CThetaPaper l ... * paperQAbsLog l logQ ≤
    CTheta l ... * paperQAbsLog l logQ.
Proof: unfold CTheta and CThetaPaper; the difference is
  CTheta*A - CThetaPaper*A =
    ((l.value:Real)+1)/4 * B * (A^2 - 1),
nonnegative from (l+1)/4 ≥ 0, B ≥ 0, A ≥ 1.

### upper_CTheta_of_upper_CThetaPaper
Given hupper : thetaLogVolume ≤ CThetaPaper*A, hA, hB, conclude
  thetaLogVolume ≤ CTheta*A.
Proof: hupper.trans CThetaPaper_mul_A_le_CTheta_mul_A.

### CTheta_ge_neg_one_of_upper_CThetaPaper
Given
  hq : Real.log qParameter ≠ 0
  hincl : -|Real.log qParameter| ≤ thetaLogVolume
  habs : |Real.log qParameter| = paperQAbsLog l logQ
  hupper : thetaLogVolume ≤ CThetaPaper*A
  hA, hB
conclude -1 ≤ CTheta l ... .
Proof: S2714_cThetaLowerBound_of_upper hq hincl with C = CTheta, after
rewriting |log q| to A and using upper_CTheta_of_upper_CThetaPaper.

Caveat: the file is source-only until watchdog compiles it. No claim of EXIT=0
or olean here. The proofs use the existing S2691/S2715/S2714 definitions; no
new axiom, no fake equality.

## 2. Scale relations used

A = paperQAbsLog l logQ.
B = cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm.
CTheta = ((l+1)/4) * A * B - 1.
CThetaPaper = ((l+1)/4 / A) * B - 1.
S2715.CThetaPaper_eq_S2691CTheta_scale:
  CThetaPaper = (CTheta+1)/A^2 - 1.
Then
  CThetaPaper*A = (CTheta+1)/A - A,
and
  CTheta*A - CThetaPaper*A = ((l+1)/4)*B*(A^2-1).
The comparison lemma is the exact condition for the desired inequality; no
equality bridge is asserted.

## 3. D19-D24 direction check (coord/XID-DETERMINANT-PLAN.md)

Paper D20-D22 (IUT III:10834-10850):
- the localizations of arithmetic vector bundles have rank > 1;
- one forms the determinant (positive tensor power) and applies normalized
  log-volume to two regions: the region 1,◦U and the region arising from the
  q-pilot object on 1,◦UQ;
- then obtains
    R_{≤−|log(Θ)|} := {λ∈R | λ≤−|log(Θ)|} ⊆ R,
    −|log(q)| ∈ R.

Important: R_{≤−|logΘ|} ⊆ R is an inclusion of a real half-line in R. It is
trivially true and does not itself assert a geometric region inclusion between
the theta hull and the q-pilot region. The content is that the q-pilot
log-volume −|log q| is a real number lying in the half-line determined by the
theta-hull log-volume −|log Θ|, i.e. −|log q| ≤ −|log Θ|.

Which geometric direction is sufficient? (Corrected A1049; abc review)
Let qPilotRegion be the region from the q-pilot representation on 1,◦UQ, with
log-volume −|log q| = −A; let thetaHullRegion be the holomorphic hull region
1,◦U, with log-volume −|log Θ| = −R. Write `logVol S = −log μ(S)`; then
`μ(qPilotRegion)=e^A`, `μ(thetaHullRegion)=e^R`. Therefore:
- the variant `−A ≤ −R` is equivalent to `A ≥ R`;
- measure monotonicity: `thetaHullRegion ⊆ qPilotRegion` ⇒ `μ(theta) ≤ μ(q)`
  ⇒ `R ≤ A` ⇒ `−A ≤ −R`: the paper inequality.
- the reverse `qPilotRegion ⊆ thetaHullRegion` gives `μ(q) ≤ μ(theta)`
  ⇒ `A ≤ R` ⇒ `−A ≥ −R`, the opposite inequality.
Thus the correct sufficient direction is
  **thetaHullRegion ⊆ qPilotRegion**,
not qPilotRegion ⊆ thetaHullRegion. This matches XID-DETERMINANT-PLAN Subgoal B
(corrected: `thetaHullRegion ⊆ qPilotRegion`) and `Mzk1QRegionInclusionActual`
(DIRECTION-VERIFIED; reverse counterexample `variant_rankone_conditional_rev`).

The paper's D22 real half-line statement is equivalent to the inequality, but it
does not by itself supply the geometric inclusion; the determinant comparison
(D20-D21) is what one needs to establish the qPilot-to-hull volume comparison.
The rank-one shadow is: the theta hull region inside the q-pilot region
(or at least `μ(thetaHull) ≤ μ(qPilot)`, i.e. `R ≤ A`).

## 4. Integration notes

- The CTheta retarget file provides the conditional scalar comparison only.
  It does not prove hscalar, does not construct CThetaPaper upper, and does not
  prove the variant.
- For N5Weak, the remaining required pieces are still: actual qPilot/theta
  region identification with the volumes, S3019MissingBridge/native q-pilot
  identification, and a lower-bound/upper-bound input for the theta hull
  (variant/SS), not just this scalar comparison.
- The D19-D24 direction check (corrected A1049) recommends **thetaHullRegion ⊆ qPilotRegion**
  as the geometric sufficient statement; proving the reverse qPilot⊆theta would give
  the opposite inequality under the standard `logVol = −log μ` convention.

No compile claimed; file handed to watchdog.


## Correction (A1055): orientation under negHaarLog

The D19-D24 direction discussion above used a log-measure signed convention.
S2717ThetaHullLogVolume is - (haarLogVolume mu thetaRegion).toReal, i.e.
negHaarLog, not log(mu). Under this convention the sufficient inclusion is
thetaRegion subset qPilotRegion (theta subset q), not qPilot subset theta.
Proof: theta subset q => mu theta <= mu q => -log mu q <= -log mu theta, which
is qLogVolume <= thetaLogVolume. The earlier qPilot subset thetaHull sentence is
correct only for the log-measure convention without the outer negation and is the
wrong direction for S2717. See coord/VOLUME-IDENTIFICATION.md sections 3-4.
