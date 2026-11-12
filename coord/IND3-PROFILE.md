# IND3-PROFILE — exact ind3_upper and wall equation (A1110)

Status: read-only; no compile.

## 1. Profile.ind3_upper (exact statement)

Source: LeanFormal/IUT/IUTIII/Theorem311/MultiradialProfileKernel.lean:13-29.

structure Profile (core : Core Label Choice) where
  logVolume : Choice -> Real
  possibleImage : Choice -> Set Real
  ind1_invariant : forall g c, logVolume (core.ind1 g c) = logVolume c
  ind2_invariant : forall g c, logVolume (core.ind2 g c) = logVolume c
  ind3_upper : forall n c, logVolume c <= logVolume (core.ind3 n c)
  possibleImage_nonempty ...
  possibleImage_ind1 ...
  possibleImage_ind2 ...
  possibleImage_ind3 ...

So ind3_upper is exactly the WEAK inequality

  logVolume c <= logVolume (core.ind3 n c)

for every n : Nat and c : Choice. There is NO additive constant, no
plus n times const, and no equality in the field type. An explicit
lower/translation bound would be separate data (VolumeTranslationData in the
K1K2 audit), not this field.

## 2. sourceStepXIProfile.ind3_upper

Source: S3138SourceProcessionProfileActual.lean:67-95.

- logVolume c := (I.family.theater c.1).thetaPacket.logVolume
  (sourceStepXILogVolume, :41).
- sourceStepXILogVolume_eq : logVolume c = logVolume c' for all c,c'
  (:59), proved from family link q-transport and FiniteThetaPacket.log_scale
  (sourceStepXIThetaLogVolume_eq, :49).
- ind3_upper is then
  le_of_eq (sourceStepXILogVolume_eq I c ((sourceStepXICore I).ind3 n c))
  (:78-80).

Thus for the constructed source profile, ind3_upper is actually an EQUALITY,
because the source log-volume is constant on all choices. It is not a genuine
volume increase. The weak field is satisfied by constancy.

Consequences:
- sourceMultiradialLogVolume_ind3_le (S3139:146) gives the weak <= for the
  descended quotient; it follows from the constant profile.
- No plus-n-const statement exists for the source profile.

## 3. K1K2 audit

Source: LeanFormal/IUT/IUTIII/Theorem311/SourceK1K2Ind3ScalingAudit.lean:1-30.

- T10 records: the packet's upper-semi law is the weak inequality
  logVolume c <= logVolume (ind3 m c).
- The volume-translation law is conditional data (VolumeTranslationData); it
  does not follow from the weak law.
- The weak <= is the only unconditional direction; a strictly positive
  translation shift would force strict increase, so it cannot be upgraded to
  equality under a translation law.
- The finite model has increase vol + n with n > 0, but that is a model, not the
  Profile field.

## 4. Wall equation A490

Source: tmp/sheaf/lana/iut/Iut/Wall/Checks.lean:52-73; EtaAlg.lean:169-190;
A490NumericalWallRhsReductionActual.lean.

- Wall (hypothesis 9-1, EtaAlg:173):
  for every pair of sides and every Theta-link gl from thetaBPS h1 to qBPS h2,
  there exist a choice iota and an Ind3 choice S with
  etaAnab iota S = etaQ.
- NumericalWall (Checks:56):
  exists U : Region D,
    IsAdelic D U
    and InHullOfImage D U
    and (qVal D.bpsDegrees).eta (logVol D U) = etaQ D.
- numericalWall_iff (Checks:61):
  NumericalWall D <-> Corollary312Variant (concreteVariantData D).
- numericalWall_iff_rss (Checks:69):
  NumericalWall D <-> exists U adelic, InHullOfImage U,
    Rss.mk D U hU = (rssEquiv D).symm (concreteVariantData D).qPilot.lhs.
- numericalWall_iff_qPilot_le_rhs
  (A490NumericalWallRhsReductionActual:17):
  NumericalWall D <-> (concreteVariantData D).qPilot.lhs <=
    (concreteVariantData D).rhsData.rhs.
- qPilot.lhs = -absLogQ (Mzk1LANAQPilotWallRegionActual:49/58); the q-pilot
  region has logVol = -qPilotScale = qPilot.lhs (:69).

So the A490 wall equation is the single numerical inequality
  qPilot.lhs <= rhs,
equivalently the existence of an adelic hull region with log-volume lhs.

## 5. Verdict

- ind3_upper is only the weak inequality logVolume c <= logVolume (ind3 n c);
  no additive n-const bound is part of the Profile.
- The constructed source profile satisfies it by equality, since the source
  log-volume is constant over choices.
- An additive/normalized translation law is separate conditional data
  (VolumeTranslationData), not a field of Profile.
- The A490 wall is the numerical inequality qPilot.lhs <= rhs; it is equivalent
  to the Corollary 3.12 variant.
