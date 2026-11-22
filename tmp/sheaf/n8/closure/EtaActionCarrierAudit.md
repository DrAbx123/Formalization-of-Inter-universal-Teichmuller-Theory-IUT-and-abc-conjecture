# ETA source-action carrier audit

Date: 2026-10-24
Auditor: transport
Audited: EtaSourceActionActual.lean and EtaSourceActionShellPreservation.lean.
No Lean files changed.

## 1. The problem

The current EtaSourceActionActual chooses

  G := (NativeShell X).K^×
  G -> (NativeShell X).K ≃ₗ[ℚ] (NativeShell X).K,  u |-> left multiplication by u

This is a field-multiplication action on the additive log-coordinate carrier K.
It is an actual group action and it has an actual norm isometry on norm-one
units, but it is NOT the source action of IUT and it does not preserve the
additive preLogShell/logShell sets.

Reason: preLogShell is the log-image of the invariant units,
  preLogShell = {a | exists u in invariants, logMap(u).toAdd = a},
and logShell = (pStar)^(-1) * preLogShell in the additive log coordinate.
These are additive subgroups/sets.  Multiplying the log coordinate by a
norm-one field element is a ℚ-linear scaling, not an additive translation or
the source group action.  Norm preservation of K is therefore irrelevant to
preservation of the shell sets; no production theorem supplies that closure.

## 2. Where the IUT source action actually acts

IUT III, Proposition 1.2, (vi) and Remark 3.10.2:
- the source group acts on the log(†D⊢_v) modules / LGP-monoids;
- the middle group acts on log(†F⊢×μ_v) packet data;
- the target group acts on log(†F_v);
- these actions are compatible with the log-link / Theta-x-mu-LGP-link and
  with the Q-span/tensor packet structures.

The production formalization expresses the correct shape in
SourceLogShellActionCompatibility:
  sourceAction i : G ->* ((D i).K ≃ₗ[ℚ] (D i).K)
  middleAction i : G ->* ((X i).K ≃ₗ[ℚ] (X i).K)
  targetAction i : G ->* ((F i).K ≃ₗ[ℚ] (F i).K)
  left_equivariant / right_equivariant with the chain supply.
There the K action is an abstract ℚ-linear automorphism supplied by the
source action data, not left multiplication by a field element.  The
production structure is conditional: it does not construct the action.

The correct IUT carrier is one of:
- LGP-monoid / LGP procession object;
- tensor packet / Q-span packet (SourceLogShellXMuPacket and the mixed/tensor
  packet constructions);
- log-link / vertical log-Kummer data (VerticalLogKummer, log-link iteration);
- source group action on the invariant units / Galois-invariant shell data.

It is not "field multiplication on K".

## 3. Current Lean carriers available

Actual carriers:
- LeanFormal.IUT.N8Closure.NativeInput.N8NativeInput;
- NativeC3.nativeFPlaceOverBad / nativeFPlaceAtPrime;
- C2Native.nativeLocalShell : SourceLogShellDatum (K, Units, invariants,
  logMap, pStar, preLogShell, logShell, IQSpan);
- SourceLogShellDatum.preLogShell / logShell / IQSpan / unitLayer;
- SourceLogShellXMuPacket (A-tensor / Q-span packet);
- SourceLogShellXMuChainSupply and SourceLogShellXMuChainActionCompatibility
  (conditional action shape with left/right equivariance);
- production SourceLGPProcession / SourcePacketRealization (IUTII Kummer
  K1K2 files);
- VerticalLogKummer / log-link iteration carriers in IUTII Kummer.

Current N8 actual action:
- EtaSourceActionActual.nativeSourceAction is field multiplication on K by
  the completion unit group.  Actual, but wrong carrier for the IUT source
  action.

Current N8 chain construction:
- EtaSourceActionShellPreservation.nativeChainSupply is D = X = F =
  nativeLocalShell with identity legs;
- nativeChainActionCompatibility uses the same field-multiplication action on
  all three sides.  Its left/right equivariance is rfl because the legs are
  identities.  It is a formal actual action-compatibility instance, but it
  does not encode the IUT source action on a non-identity chain.

## 4. Exact gaps

C1. Correct source-action carrier:
    construct the action on the LGP-monoid / packet / log-link carrier, not on
    K by field multiplication.

C2. Source group:
    the current group is the completion unit group K^×.  The IUT source group
    is the source Galois/Theta group acting through the LGP/packet/log-link
    structure; no actual N8 group action on those carriers is constructed.

C3. Actual LGP carrier in N8:
    SourceLGPProcession / SourcePacketRealization exist in production K1K2
    files, but no N8 native-to-LGP construction is present.

C4. Actual log-link action:
    VerticalLogKummer / log-link iteration data are production records; no N8
    actual action on the native log-shell chain is constructed.

C5. Shell preservation:
    preLogShell/logShell are additive log-coordinate sets.  Norm-one field
    multiplication is not an additive shell operation; the set-preservation
    target is not a consequence of norm preservation.  The exact target
    NormOneUnitShellPreservation remains open; only the identity unit is an
    actual preservation witness.

C6. Non-identity chain:
    the actual chain supply uses identity legs.  A source action must be
    compatible with non-identity LGP/packet legs; no such actual chain is
    constructed.

C7. IUT compatibility:
    no N8 square/proof that the LGP action is compatible with the
    log-link or the tensor packet and with the Q-span/log-volume data.

## 5. Correction

Do not treat EtaSourceActionActual.nativeSourceAction as the IUT source
action.  Archive it as an actual norm-isometry/field-scaling action, not as
the source action.

Correct next target:

1. Define an N8 source-action carrier C from an actual LGP/packet/log-link
   object:
   C := SourceLGPProcession (or SourceLogShellXMuPacket / VerticalLogKummer).
2. Define the source group G with its actual action on C, not on K by field
   multiplication.
3. Reuse SourceLogShellXMuChainActionCompatibility only as the exact
   conditional interface; fill its sourceAction/middleAction/targetAction with
   the actual LGP/packet actions, not with left multiplication on K.
4. Prove action laws on C and the left/right equivariance for an actual
   non-identity chain supply.
5. Only after that state shell/region/log-volume preservation; do not derive
   it from norm isometry.

## 6. Next package checklist

- EtaSourceActionCarrierCorrected.lean:
  exact carrier type for the source action (LGP/packet/log-link), actual
  construction or exact named gap; no field multiplication.
- EtaSourceGroupActual.lean:
  exact source group and actual action on the corrected carrier; action laws.
- EtaSourceActionChainActual.lean:
  actual non-identity chain supply and SourceLogShellXMuChainActionCompatibility
  filled with the corrected actions; equivariance actual or exact gap.
- EtaSourceActionShellPreservationCorrected.lean:
  only after the corrected action, state the logShell/preLogShell preservation
  target; no norm-isometry substitution.
- Audit:
  reject any action on K by field multiplication as an IUT source action.

## 7. Status

The current unit action is actual but carrier-wrong for the IUT source action.
The actual chain supply/action compatibility are formal and identity-legged;
they do not encode the source action on LGP/tensor packet/log-link data.
The exact gaps are C1-C7.  No Lean file was modified.
