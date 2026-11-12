# QPILOT-HAAR-REGION — candidate qPilotHaarRegion and the common-mu gap

Status: READ-ONLY CANDIDATE PLAN, 2026-11-12. No Lean file, no compile.
Related: coord/VOLUME-IDENTIFICATION.md; S2717Cor312FullTargetActual,
S2807ThetaHullVolumeIdentityActual, HullDetObjectActual,
GlobalIQHullInterfaceActual, LiteralIQCarrierConstructionActual.

## 1. Exact types already present

Theta side (common mu is actual C3 tensor Haar):
- S2717ThetaHullLogVolume (S2717Cor312FullTargetActual:50-67)
    = - (globalThetaHullInterface.logVolume globalThetaHull).toReal.
- S2807_thetaHullVolume_eq_haarRegion (S2807ThetaHullVolumeIdentityActual:40-47)
    = - (haarLogVolume (actualC3LogShellTensorHaar C3)
          (actualC3LogShellTensorRegion C3)).toReal.
Thus thetaLogVolume = negHaarLog mu thetaRegion, with
  mu = actualC3LogShellTensorHaar C3,
  thetaRegion = actualC3LogShellTensorRegion C3,
and S2807_paperCor312Full_iff_haarRegion rewrites PaperCor312Full on this mu.

Q side candidates:
- S2717QPilotLogVolume (S2717:69-76) = sourceQPilotSignedLog I.initial.
- HullDetObjectActual.qPilotLogVolume (HullDet:158-165)
    = -|Real.log (‖P.line.C3.q.q‖)|.
- S3016StepVQPilot (S3016:30) = S2736QPilotLineBundleLogVolume (S2752J ...).
- S3016WeightedGlobalQPilot = nativeGlobalQPilotNormalizedLogMagnitude T.
- HullDet literalIQHull (HullDet:180-185) = globalIQHull,
  with ambient GlobalIQAmbient C3 n, not C3LogShellTensorBlock C3.
- GlobalIQUnitRegion/literalIQUnitRegion have Haar log-volume on
  GlobalIQAmbient C3 n (literalIQHaar), not the C3 tensor Haar.

## 2. Why a literal common-mu definition is not available

The theta common mu lives on:
  C3LogShellTensorBlock C3 = ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple
  (a tensor over C3.tensorIndex).
The global q-side hull/unit region lives on:
  GlobalIQAmbient C3 n = ArithmeticPacketTensor (literalIQPlaces C3 n),
  with index Fin (n+1) x C3.tensorIndex.
These are different ambient spaces and different Haar measures. No theorem in the
audited files constructs a measure-preserving equivalence
  GlobalIQAmbient C3 n ~= C3LogShellTensorBlock C3
or a q-pilot region in C3LogShellTensorBlock C3.

Therefore one cannot honestly define
  qPilotHaarRegion : Set (C3LogShellTensorBlock C3)
by transporting literalIQHull without new data/theorems. Likewise
S2717QPilotLogVolume, HullDet.qPilotLogVolume and S3016StepVQPilot are scalars /
line-bundle log-volumes, not integrals over a C3 Haar region.

## 3. Honest candidate definitions

Option A (new C3-block region; requires real construction):
  noncomputable def qPilotHaarRegion
      (C3 : SourcePilotRegionData (l := l) (V := V) I) :
      Set (C3LogShellTensorBlock C3) :=
    <the actual q-pilot line/tensor localization region at (1,0), constructed
     from the C3 tensor places and the q-pilot line; body not yet available>
This cannot be filled from current files; its body is the missing construction.
Do not define it as thetaRegion or as Set.univ by hand.

Option B (bridge record; explicit target data, no fake inhabitant):
  structure QPilotHaarRegionData
      (C3 : SourcePilotRegionData ...) where
    region : Set (C3LogShellTensorBlock C3)
    region_measurable : MeasurableSet region
    region_lt_top : (actualC3LogShellTensorHaar C3) region < top
    volume_eq :
      S2717QPilotLogVolume ... =
        - (haarLogVolume (actualC3LogShellTensorHaar C3) region).toReal
    theta_subset_region :
      actualC3LogShellTensorRegion C3 subset region
This is the exact remaining identification packaged as data. It does not assert
an inhabitant.

Option C (global ambient route; conditional on a new equivalence):
  use literalIQHull C3 n as a q-side region, but require
    e : GlobalIQAmbient C3 n ~= C3LogShellTensorBlock C3
  and a measure-compatibility proof. Neither e nor the measure compatibility is
  in the tree; this is a GAP, not a definition.

## 4. Candidate theorem statements

Assuming Option B data, the signed inequality is formally derivable:

  theorem qPilotLogVolume_le_thetaHullLogVolume_of_bridge
      (B : QPilotHaarRegionData C3) :
      S2717QPilotLogVolume ... <=
        S2717ThetaHullLogVolume ... := by
    -- theta side: S2807_thetaHullVolume_eq_haarRegion
    -- q side: B.volume_eq
    -- inclusion B.theta_subset_region (theta subset q)
    -- monotonicity haarLogVolume_mono
    -- negate: -H q <= -H theta, i.e. qLog <= thetaLog

The subset direction is thetaRegion subset qPilotRegion, not the reverse:
  theta subset q => H theta <= H q => -H q <= -H theta => qLog <= thetaLog.
This matches the negHaarLog normalization of S2717 (see VOLUME-IDENTIFICATION.md
section 3).

If one insists on a q subset theta statement, it would give the opposite
inequality under -haarLog and is not the paper direction.

## 5. Reusable pieces and exact missing declarations

Reusable:
- S2807_thetaHullVolume_eq_haarRegion / S2807_paperCor312Full_iff_haarRegion;
- haarLogVolume_mono (FinitePlaceIQHullInterface:68);
- globalIQLogVolume_mono / globalIQUnitRegion_compact for the global side;
- HullDet literalIQHull/literalIQHullLogVolume as a candidate global q-side region
  (different mu; cannot be used directly on C3 block);
- S3016StepVQPilot/S3019 reductions for the scalar q-pilot line bundle, once a
  Haar region equality is supplied.

Missing declarations (minimal):
1. qPilotHaarRegion in C3LogShellTensorBlock (or QPilotHaarRegionData.region);
2. qPilotLogVolume_eq_negHaarLog: qPilot scalar = -H qRegion;
3. thetaRegion_subset_qPilotRegion;
4. measurable/finite side conditions for qRegion;
5. assembly theorem above.

## 6. Verdict

- Theta side is fully on the actual C3 Haar mu (S2807 exact).
- Q side is not: all current candidates are scalars/line-bundle volumes, and
  literalIQHull lives on a different global ambient with a different Haar.
- A qPilotHaarRegion definition is not available from current files; the honest
  form is the explicit QPilotHaarRegionData bridge with volume equality and
  theta subset q.
- The correct orientation under S2717's -haarLog is theta subset q, not q subset
  theta.
- No fake definition or equality is proposed; no Lean file written and no
  compile claimed.
