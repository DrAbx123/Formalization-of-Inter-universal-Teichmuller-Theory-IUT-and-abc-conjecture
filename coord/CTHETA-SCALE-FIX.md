# CTHETA-SCALE-FIX — paper CTheta vs CThetaPaper and the hscalar target

Status: READ-ONLY audit, 2026-11-12. No Lean file, no compile.
Sources: S2691ExactQNormalizationActual.lean:51-135, 231-279;
S2715CThetaPaperScaleActual.lean:11-98; S2714CThetaUpperInventoryActual.lean;
S2807SG3aActual.lean:42-60; S2807SG3bScalarActual.lean:44;
S2819ScalarBracketActual.lean; S3025ActualThetaUpperAudit.lean;
S3034PacketScalarBoundActual.lean.

## 1. Exact definitions/signatures

A = paperQAbsLog l logQ = logQ/(2l) (S2691:55).
B = cThetaBracket l logQ dmod dFpd fFpd eStar etaPrm (S2691:103):
  B = (1+12 dmod/l)(log dFpd + log fFpd) + 10(eStar*l + etaPrm)
      - (1/6)(1-12/l^2) logQ.

S2691 CTheta (called the printed formula):
  CTheta = ((l+1)/4) * A * B - 1.
S2715 CThetaPaper:
  CThetaPaper = ((l+1)/4 / A) * B - 1.

S2715 exact relation:
  CThetaPaper = (CTheta + 1) / A^2 - 1
  (CThetaPaper_eq_S2691CTheta_scale, assuming A != 0).
Hence:
  CThetaPaper * A = (CTheta + 1)/A - A,
and generally CThetaPaper * A != CTheta * A.
For A = 1 they coincide; for general A they do not.

S2807/S2807b/S2819/S3025/S3034 all currently use CThetaPaper * A
(= CThetaPaper * paperQAbsLog) as the RHS of the scalar upper:
  - S2807_upperGap_iff_neg_tensorLogVolume:
      -actualC3LogShellTensorLogVolume <= CThetaPaper * A;
  - S2807_upperGap_of_packetLogVolume_le:
      hscalar : -packetLogVolume <= CThetaPaper * A;
  - S2819_scalar_iff_CTheta_ge:
      -packetLogVolume <= CThetaPaper * A <-> -packet/A <= CThetaPaper;
  - S3025MissingThetaUpperScalar / S3034_hscalar_iff:
      -actualC3LogShellTensorLogVolume <= CThetaPaper * A.

## 2. Correct paper upper target

Paper Cor 3.12/Thm 1.10 uses CTheta as the constant in
  -|log Theta| <= CTheta * |log q|.
With A = |log q| and thetaLogVolume = -actualC3LogShellTensorLogVolume
(S2807 identifies thetaHullVolume with its negative), the correct target is

  thetaLogVolume <= CTheta * A.

The current hscalar target is instead
  thetaLogVolume <= CThetaPaper * A.
These are not the same; the hscalar RHS is not CTheta*A.

## 3. S2714_cThetaLowerBound_of_upper

Exact statement (S2714CThetaUpperInventoryActual):
  theorem S2714_cThetaLowerBound_of_upper
    {theta q : Real} (hq : Real.log q != 0)
    (hincl : -|Real.log q| <= theta) {C : Real}
    (hupper : theta <= C * |Real.log q|) : -1 <= C
  = cor312CThetaLowerBound hq hincl hupper.

It consumes a correct upper target theta <= C*A and the inclusion -A <= theta,
and produces -1 <= C. It does NOT prove the upper target; it is a lower-bound
consumer. If hscalar is restated with CTheta, then S2714 gives -1 <= CTheta.
With CThetaPaper (or its A-scaled form) the same consumer gives
-1 <= CThetaPaper, which by S2715 is equivalent to -1 <= CTheta (both are
equivalent to B >= 0 under A>0), so the lower-bound transfer is insensitive
to the scale mismatch; only the upper target is wrong.

## 4. Step (v) and 1/6 log q

S2691 CTheta_ge_neg_one_iff:
  -1 <= CTheta <-> B >= 0,
  i.e. (1/6)(1-12/l^2) logQ <= (1+12 dmod/l)(log dFpd+log fFpd)
       + 10(eStar*l+etaPrm).

S2691 CTheta_ge_neg_one_implies_log_bound:
  -1 <= CTheta (plus 7<=l, 1<=dmod, log dFpd+log fFpd>=0, eStar*l+etaPrm>=0)
  => (1/6) logQ <= (1+20 dmod/l)(log dFpd+log fFpd) + 20(eStar*l+etaPrm).

This is one-way: CTheta>= -1 implies the 1/6 bound. The paper's final displayed
1/6 bound has coefficients 20/20 and is weaker/different from the exact bracket
inequality (12/10). There is no theorem in the audited files proving the
converse from the final 1/6 bound back to -1 <= CTheta. To derive -1 <= CTheta
from Step (v), one needs the exact bracket inequality (before the 20/20
absorption) plus the positivity assumptions; the audited S3015/S3017 stack gives
the height/upper bound, not this exact bracket inequality.

## 5. Bridge CThetaPaper*A <-> CTheta*A

An equality bridge is not available and should not be assumed:
  CThetaPaper*A = (CTheta+1)/A - A,
  CTheta*A = CTheta*A.
Equality would force a nontrivial relation between A and CTheta; false for
generic A. Adding it as an axiom would be fake.

A useful conditional INEQUALITY bridge:
  CThetaPaper*A <= CTheta*A
  <-> (CTheta+1)/A - A <= CTheta*A
  <-> ... equivalently B*(A^2-1) >= 0 using CTheta=A*B-1 and
      CThetaPaper=B/A-1.
Thus if A >= 1 and B >= 0, then CThetaPaper*A <= CTheta*A. Then the existing
hscalar (upper with the smaller CThetaPaper*A) implies the correct upper with
CTheta*A. If A < 1, the inequality reverses and hscalar does NOT imply the
correct target.

So the shortest conditional repair is:
  hA1 : 1 <= A
  hB : 0 <= B (or 0 <= CTheta+1)
  CThetaPaper_mul_A_le_CTheta_mul_A : CThetaPaper*A <= CTheta*A
  then trans hscalar (this inequality) gives thetaLogVolume <= CTheta*A.
No fake equality is needed. The equality bridge remains false in general.

## 6. Minimal fix options

Option A (cleanest, no false bridge):
1. Define/use S2691 CTheta as the constant in S2807/S3025/S3034 targets:
   replace CThetaPaper*A by CTheta*A.
2. Add the exact comparison lemma
   CThetaPaper_mul_A_le_CTheta_mul_A under 1<=A and 0<=B, for consumers that
   still use CThetaPaper.
3. Use S2714_cThetaLowerBound_of_upper to get -1<=CTheta from the corrected
   upper; then S2691 CTheta_ge_neg_one_iff / log_bound for the final 1/6 bound.
Cost: edit S2807_upperGap_iff_neg_tensorLogVolume, S2807_upperGap_of_packetLogVolume_le,
S2819 lemmas, S3025MissingThetaUpperScalar, S3034_hscalar_iff, plus any consumers.
The definitions CTheta/CThetaPaper already exist; no new mathematics is needed
for the target statement.

Option B (minimal edits, conditional):
Keep hscalar with CThetaPaper*A, add the inequality bridge
CThetaPaper*A <= CTheta*A under 1<=A, 0<=B, and a corrected upper target
thetaLogVolume <= CTheta*A as a theorem. This is shorter but proves the correct
upper only under A>=1,B>=0; it does not fix hscalar's target itself.

Option C (not acceptable): add equality CThetaPaper*A=CTheta*A or redefine
CThetaPaper to CTheta without updating its relation theorem; the former is
false, the latter breaks S2715 CThetaPaper_eq_S2691CTheta_scale and S2819.

## 7. Verdict

- The scale mismatch is real: CTheta = A*B-1, CThetaPaper = B/A-1;
  CThetaPaper = (CTheta+1)/A^2 -1; CThetaPaper*A != CTheta*A generally.
- hscalar's RHS is CThetaPaper*A, not the paper CTheta*A.
- S2714_cThetaLowerBound_of_upper can transfer a correct upper to -1<=CTheta,
  but does not produce the upper. The 1/6 bound is a one-way consequence of
  -1<=CTheta, not a route back without the exact bracket inequality.
- An equality bridge between CThetaPaper*A and CTheta*A is infeasible/false.
  The feasible shortest repair is either (A) retarget CTheta, or (B) use the
  inequality CThetaPaper*A <= CTheta*A under A>=1 and B>=0.
- No Lean file written; no compile claimed.
