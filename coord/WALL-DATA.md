# WALL-DATA — NumericalWall fields and instantiation status (A1112)

Status: read-only; no compile.

## 1. Source files / olean status

- tmp/sheaf/lana/iut/Iut/Wall/Checks.lean (NumericalWall, numericalWall_iff)
  olean: NO.
- tmp/sheaf/lana/iut/Iut/Wall/Rss.lean (Region, InHullOfImage, thetaImage,
  hullOf, IsAdelic, Rss, etaQ)
  olean: NO.
- tmp/sheaf/lana/iut/Iut/Wall/BPS.lean (ValBPS, eta, eta_pilot, eta_bijective)
  olean: NO.
- tmp/sheaf/lana/iut/Iut/Wall/Pilots.lean (qVal, LocalDegrees, bpsDegrees)
  olean: NO.
- tmp/sheaf/lana/iut/Iut/Wall/EtaAlg.lean (Wall, etaAnab)
  olean: NO.
- tmp/sheaf/lana/iut/Iut/Wall/QPilotRegion.lean (qRegion, etaQReg)
  olean: NO.
- tmp/sheaf/lana/iut/Iut/Wall/NumericalWallActual.lean
  olean: NO.
- tmp/external/ported/lana_core and lana_tgfree Wall files
  olean: NO.
- tmp/sheaf/xif/paper/A490NumericalWallRhsReductionActual.lean
  olean: NO.
- tmp/sheaf/xif/paper/A490WallThetaShiftAlignmentActual.lean
  olean: NO.
- tmp/sheaf/lana overall has 145 oleans, but no Wall/Checks etc.

So all wall data are source-level only at present.

## 2. Actual definitions

Region (Rss.lean): Region D := forall i : Fin (nC D), Set (some local tensor/region type).
IsAdelic (Rss.lean): adelic region predicate.
InHullOfImage (Rss.lean:338):
  def InHullOfImage (U : Region D) : Prop :=
    exists l : forall i : Fin (nC D), InitialThetaData.Lab (nC D) i,
      forall i, U i <= hullOf D (thetaImage D l) i.
thetaImage (Rss.lean:333):
  thetaImage l := D.thetaPilotOn (nC D) (fun i => {l i}) (fun _ => singleton_nonempty _).
hullOf (VcI.lean): hullOf D R := leastHull region of R.
IsAdelic (Rss.lean): adelic region.

ValBPS.eta (BPS.lean:320):
  def eta (B : ValBPS V bad) (x : Real) : B.C ->_l[Real] Real :=
    x • B.pilotCoord.toLinearMap.
So eta is just scalar multiplication of the pilot coordinate; it exists for every x
once qVal is available.

qVal (Pilots.lean:106):
  def qVal : ValBPS V L.bad where
    C := Real
    localPilot := L.deg
    ...
etaQ (Rss.lean:501):
  def etaQ : (qVal D.bpsDegrees).C ->_l[Real] Real :=
    (qVal D.bpsDegrees).eta D.qPilot.lhs.

NumericalWall (Checks.lean:56):
  def NumericalWall : Prop :=
    exists U : Region D, IsAdelic D U and InHullOfImage D U
      and (qVal D.bpsDegrees).eta (logVol D U) = etaQ D.

Wall (EtaAlg:173):
  forall sides and Theta-links, exists choice iota and Ind3 S,
    etaAnab iota S = etaQ D.
etaAnab (EtaAlg:145):
  etaAnab iota S := B.val.eta (logVol D (A.out iota S)).
etaAnab_eq_etaQ_iff (EtaAlg:151):
  etaAnab iota S = etaQ D <-> logVol D (A.out iota S) = qPilot.lhs.

A490 reductions:
- numericalWall_iff (Checks:61): NumericalWall D <-> Corollary312Variant.
- numericalWall_iff_rss (Checks:69): ... <-> exists adelic U in hull with
  Rss.mk U = rssEquiv.symm qPilot.lhs.
- numericalWall_iff_qPilot_le_rhs (A490NumericalWallRhsReduction:17):
  NumericalWall D <-> qPilot.lhs <= rhs.
- wall_thetaShift_logVol (A490WallThetaShiftAlignment:15):
  under Wall and ThetaShift, exists S with
  -(sFactor * absLogQ) + logVol D S.1 = qPilot.lhs.

## 3. Can we instantiate InHullOfImage and eta after Gap/VcI/ThetaRegion?

After Gap/VcI/ThetaRegion compile, the following are available:
- thetaImage, hullOf, Region, hull; hence InHullOfImage can be stated.
- Admissibility/hull lemmas for thetaImage (thetaImage_isAdmissible, Rss:346),
  and InImage -> InHullOfImage (Rss:350).

InHullOfImage is TRIVIALLY instantiable: choose U := hullOf D (thetaImage D l)
for any label l. Then for all i, U i <= hullOf D (thetaImage D l) i is rfl.
The only extra input is a label l (Nonempty of forall i, Lab i), which is the
source label nonemptiness, available from InitialThetaData.ivLabels_nonempty.

eta is instantiable once qVal is available: eta B x := x • pilotCoord, and
qVal D.bpsDegrees is built from the bad-degree data (bpsDegrees) in
InitialThetaData. No analytic q/theta content is needed for the map itself.

But NumericalWall additionally requires:
1. U adelic (for U = hullOf thetaImage, this follows from thetaImage
   admissibility and hull admissibility);
2. eta (logVol D U) = etaQ D, i.e. logVol D U = qPilot.lhs.
For U = hullOf thetaImage, logVol D U = rhs (rhs_eq_logVol, Rss:356), so the
condition is exactly qPilot.lhs = rhs, which is false in general; the actual
NumericalWall needs qPilot.lhs <= rhs and a region with that log-volume
(hullActual_exists_adelic_inHullOfImage_logVol, in NumericalWallHullActual).

Thus:
- InHullOfImage: YES, trivially via U = hullOf thetaImage (after port).
- eta: YES, from qVal.
- etaQ: YES, from qVal and qPilot.lhs.
- NumericalWall: NO unconditionally; equivalent to qPilot.lhs <= rhs
  (A490), i.e. the Corollary 3.12 variant. The port gives the interface, not
  the inequality.

## 4. Exact remaining dependencies

- Wall/Checks, Wall/Rss, Wall/BPS, Wall/Pilots, Wall/EtaAlg, Wall/QPilotRegion
  and Wall/NumericalWallActual must be ported/compiled.
- D.bpsDegrees and D.qPilot data come from InitialThetaData (Basic/Cor312),
  not from Gap/VcI alone.
- InHullOfImage/eta are not the hard part; the hard part is the log-volume
  equality/inequality with qPilot.lhs.

## 5. Verdict

- Definitions: NumericalWall (Checks:56), InHullOfImage (Rss:338), eta
  (BPS:320), etaQ (Rss:501), Wall (EtaAlg:173).
- InHullOfImage and eta are instantiable after the port; InHullOfImage even
  trivially with U = hullOf thetaImage.
- NumericalWall is equivalent to qPilot.lhs <= rhs; it remains the A490
  inequality, not automatic from the port.
- No wall olean currently exists; all files source-only.
