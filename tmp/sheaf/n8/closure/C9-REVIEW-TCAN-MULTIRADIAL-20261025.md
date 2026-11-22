# C9 review: T_can and paper target identity

Task: task-411. Reviewer: multiradial. Date: 2026-10-25.
Review only; no rewrite, no Lean/Project edits, no mixed/E3. Deliverable: this
file only. target_accepted=false; P6 open.

## 0. Reviewed statement

T_can as used in the NL P6 proofs:

    (C1) C9Hull = IIIHull
         = source holomorphic hull of the union of possible images of the
           Theta-pilot object under Ind1/Ind2/Ind3;
    (C2) C9QPilot = IIIQPilot
         = source q-pilot object q_v at v in V_bad, with 2l=82 root
           normalization qhat^82=q_v;
    (C3) C9LogVol = III procession-normalized mono-analytic log-volume
         (B_I-zero/C6/procession alignment).

Under T_can, the NL canonical proof concludes
    h_C^canon = H_III, Q_C^canon = Q_III, hence P6_can Q_C^canon<=h_C^canon.

Question: is T_can a paper-target definition (therefore legitimate, no extra
assumption), or an extra assumption? Compare with the normalized Lean target.

## 1. Verdict

PARTIAL ACCEPT / PARTIAL REJECT.

  - (C1) hull identity: ACCEPTED as a definitional target identity for the
    C9Paper ThetaPaper structure. C9Paper explicitly defines
    thetaHull = I.sourceHolomorphicHull and requires containment of the actual
    possible-theta image set. This is definitional, not an extra theorem.
    Caveat: it is definitional only within ThetaPaper; ThetaPaper itself is a
    target structure with named donor obligations (thetaPaper_nonempty,
    thetaToC6 interface). It is not a source theorem that every abstract C9
    target hull equals IIIHull.
  - (C2) q-pilot identity: REJECTED as definitional. C9Paper QPaper does NOT
    define its q-pilot as the source q-pilot q_v. It defines QPaper.scalar =
    localSignedLog(C3.q) and qPilotLogVolume = scalar; C3 is a SourcePilotRegion
    C3, not identified with the III q-pilot q_v in C9Paper. No C9Paper
    declaration states C3.q=q_v, qhat^82=q_v, or QPaper.qPilotLogVolume=
    -|log q|_III. This is an exact missing source identification, not a
    definition.
  - (C3) normalized volume identity: ACCEPTED for the normalized/C6-aligned
    Lean target, not for canonical P6. PaperP6C6AlignedTarget proves
    normalizedTheta = C6 normalizedLogVolume(c6Hull) and
    qLog = C6 normalizedLogVolume(qPilotRegion); PaperP6NormalizedTarget is
    actual. This is the normalized target, not canonical P6_can.
  - T_can as a *canonical paper target definition*: REJECTED. The canonical
    C9Paper QPaper uses localSignedLog = QPaper (canonical), while the Lean
    normalized target uses QPaperNorm=QPaper/d and normalizedTheta. T_can
    cannot identify canonical Q/h with normalized target values without the
    factor d=41. The claim "C9 target = paper target" is not uniform: hull
    part definitional in ThetaPaper; q-pilot/volume part not definitional;
    canonical vs normalized target distinct.

Therefore T_can is not an extra assumption in full, but it is also not a
definition in full. It is:
  - definitional for the C9Paper ThetaPaper hull (C1);
  - an exact gap for the q-pilot identity (C2);
  - definitional for the normalized/C6-aligned target (C3 in normalized
    convention), not for canonical P6_can.

## 2. Exact Lean target evidence

### 2.1 Hull identity is definitional in C9Paper ThetaPaper

C9Paper.lean lines 97-115:

    structure ThetaPaper ... where
      thetaHull : Set (I.ThetaPilotPoint D.place.v)
      thetaHull_eq : thetaHull = I.sourceHolomorphicHull D.place.v D.place.R n
      thetaHull_contains_image :
        I.possibleThetaPilotImageSet ... ⊆ thetaHull
      thetaToC6 : Set ... -> Set (C6IQCarrier places tuple)
      thetaLogVolume : WithTop Real
      thetaLogVolume_eq :
        thetaLogVolume = (C6.normalizedLogVolume (thetaToC6 thetaHull) : WithTop Real)
      ...

The equality thetaHull = sourceHolomorphicHull is a field of the structure:
C9Hull is DEFINED as the source hull inside ThetaPaper. This is the
definitional part of T_can (C1), conditional on ThetaPaper existence and the
thetaToC6 interface. ThetaPaper existence is a named sorry
(thetaPaper_nonempty), so the definitional identity is not an unconditional
source theorem.

### 2.2 Q-pilot identity is NOT definitional in QPaper

C9Paper.lean lines 63-95:

    structure QPaperScalar ... where
      value : Real
      value_eq : value = localSignedLog C3.q

    structure QPaper ... where
      qPilotRegion : Set ...
      qPilotRegion_eq_unit : qPilotRegion = {C3.tensorUnit}
      scalar : QPaperScalar C3
      kummer : SourceLogKummerData I C1
      qPilotLogVolume : WithTop Real
      qPilotLogVolume_eq : qPilotLogVolume = (scalar.value : WithTop Real)

    def qPaperOfC3 ... where
      scalar := { value := localSignedLog C3.q, value_eq := rfl }
      qPilotLogVolume := (localSignedLog C3.q : WithTop Real)

There is no field/equality C3.q = source q_v, no qhat^82=q_v, and no
QPaper.qPilotLogVolume = -|log q|_III. QPaper_qPilotLogVolume is the
localSignedLog of the C3 scalar. Therefore T_can(C2) is an EXTRA source
identification, not a definition. The exact missing statements are:
  (C2a) C3.q = q_v at the selected bad place (source q-pilot);
  (C2b) qhat^82=q_v (2l=82 normalization);
  (C2c) localSignedLog(C3.q) = -|log q|_III (source packet log-volume).

### 2.3 Normalized Lean target is actual but different

PaperP6NormalizedValuesActual.lean lines 33-74:

    normalizedTheta := thetaLogVolume S / d S
    normalizedValue T := log(c6UnitRefNormalizedData T)/d S
    normalizedValueSet := {z | exists T in allQPilotRegions, z=normalizedValue T}
    normalizedValueSet_bounded : forall z in normalizedValueSet, z<=normalizedTheta
    qLog_mem_normalizedValueSet : log||qUnit|| in normalizedValueSet
    qLog_le_normalizedTheta : log||qUnit||<=normalizedTheta
    PaperP6NormalizedTarget := (forall z in normalizedValueSet, z<=normalizedTheta)
      ∧ log||qUnit||<=normalizedTheta
    paperP6NormalizedTarget_actual : PaperP6NormalizedTarget S

This target is actual for the normalized/C6 volumes; it does not assert
C9Hull=IIIHull or C9QPilot=IIIQPilot. It uses allQPilotRegions and
normalizedValueSet, not the III possible-image hull directly. PaperP6C6AlignedTarget
adds the C6 bridge:
  normalizedTheta = C6 normalizedLogVolume(c6Hull);
  qLog = C6 normalizedLogVolume(qPilotRegion).
This is normalized, not canonical.

C9Paper target obligations:
  - qPaper_in_Rleq_obligation : QPaperInRleq ... := by sorry
  - valuesPaper_bounded_obligation : ValuesBounded ... := by sorry
  - qPaper_approximated_obligation : QPaperApproximated ... := by sorry
  - thetaPaper_nonempty : Nonempty ThetaPaper := by sorry
  - valuesPaper_nonempty : Nonempty ValuesPaper := by sorry
These are target-structure/donor gaps; T_can does not remove them.

### 2.4 Canonical factor

C7QPaperNormalized.lean lines 10-16:
  QPaper = log(qPilotMass) = d*log||q||; QPaperNorm := QPaper/d.
C9Paper QPaper.scalar = localSignedLog(C3.q) = canonical Q.
PaperP6NormalizedTarget uses normalized Q = log||qUnit||.
Thus:
  canonical QPaper = d * normalized PaperP6 qLog = 41*normalized in tame type.
  canonical h = d * normalized h.
P6_canon Q_canon<=h_canon is equivalent to P6_norm Q_norm<=h_norm if BOTH
sides are canonical/normalized consistently. T_can as stated for canonical
objects is not the normalized Lean target; identifying them without factor 41
is rejected.

## 3. Accept/reject table

| T_can component | verdict | exact reason |
|---|---|---|
| C1 C9Hull=IIIHull | ACCEPT (definitional in ThetaPaper) | ThetaPaper.thetaHull_eq = sourceHolomorphicHull; definitional, conditional on ThetaPaper donor/thetaToC6 |
| C1 as theorem for arbitrary abstract C9Hull | REJECT | only definitional if C9Hull is defined as source hull; no source theorem identifies an abstract target |
| C2 C9QPilot=IIIQPilot | REJECT (extra assumption/gap) | QPaper uses C3.q/localSignedLog, no C3.q=q_v/qhat^82/-|logq| identity |
| C3 C9LogVol=III log-vol | ACCEPT for normalized/C6 target | PaperP6C6AlignedTarget actual C6 bridge; not canonical |
| T_can canonical paper target identity | REJECT | canonical QPaper=d*normalized; P6_can and PaperP6NormalizedTarget differ by d=41; normalized Lean target is a different theorem |
| T_can unconditional paper target | REJECT | C1 conditional on ThetaPaper donor, C2 missing, C9Paper Rleq/values/approximation sorries remain |

## 4. Consequences for the NL proofs

  - Canonical P6_can (task-406): T_can is not fully definitional. C1 hull part
    may be accepted as definitional within ThetaPaper; C2 q-pilot identity is
    an exact gap. Therefore SORRY_TCAN remains, split as:
      T_CAN_HULL: definitional in ThetaPaper, conditional on donor;
      T_CAN_QPILOT: exact missing C3.q=q_v/82-root/source log;
      T_CAN_VOLUME: normalized/C6 bridge actual; canonical factor d must be
        handled separately.
  - Normalized P6_norm: does not need T_can in the form C9Hull=IIIHull;
    PaperP6NormalizedTarget is actual for normalizedValueSet/normalizedTheta,
    with qLog membership. T_can is unnecessary/incorrect as a canonical bridge.
  - C9Paper target: still has named sorries qPaper_in_Rleq, valuesPaper_bounded,
    qPaper_approximated, thetaPaper_nonempty, valuesPaper_nonempty. T_can does
    not discharge them.
  - Canonical P6_can cannot be obtained by declaring T_can; it needs the
    q-pilot identity and canonical factor. The normalized Lean target cannot
    substitute for canonical P6_can.

## 5. Exact reasons summary

ACCEPT:
  - ThetaPaper hull equality is definitional (C9Paper.lean thetaHull_eq);
  - normalized/C6 volume bridge is actual (PaperP6C6AlignedTarget);
  - normalized PaperP6 target is actual (PaperP6NormalizedValuesActual).

REJECT as definitional/paper target:
  - QPaper q-pilot identity: no source q_v/82-root/localSignedLog equality;
  - T_can as arbitrary abstract C9 hull identity;
  - T_can as canonical-vs-normalized target identity without factor 41;
  - T_can as eliminating C9Paper qPaper_in_Rleq/valuesPaper_bounded/
    qPaper_approximated/thetaPaper_nonempty/valuesPaper_nonempty.

No mixed/E3 profile is involved. No new source theorem is introduced by this
review; it only accepts/rejects the existing T_can statement.

## 6. Status

Review verdict: PARTIAL ACCEPT / PARTIAL REJECT. T_can is definitional for the
C9Paper ThetaPaper hull; it is an extra assumption/gap for the q-pilot identity
and for canonical/normalized target identification. Canonical P6_can is not
closed; normalized Lean target is a separate actual theorem. No Lean/Project
edits; target_accepted=false; P6 open.

## 7. Acceptance

Only C9-REVIEW-TCAN-MULTIRADIAL-20261025.md written. Review only; no rewrite of
the reviewed files; no Lean/Project/target edits; no independent review/kernel/
comparator run. target_accepted=false.
