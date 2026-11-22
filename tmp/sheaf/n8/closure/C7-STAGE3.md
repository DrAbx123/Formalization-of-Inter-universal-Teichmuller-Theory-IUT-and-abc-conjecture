# C7 STAGE3: actual SourceHolomorphicHullData closure

Task S3-C7. Consumer: sourceHolomorphicHullData_nonempty (C7 stage-2 file).

## 1. Target

~~~text
SourceHolomorphicHullData (C1) (C2) (C3) (D) (C5) mu B T n
~~~

on the actual IQ carrier C6IQCarrier C3.tensorPlaces C3.tensorTuple. Fields:
- iqHull_eq : B.iqInterface.hull = commonHull C3 mu B
- image_subset_hull : permittedImage T n ⊆ commonHull C3 mu B
- contains_permitted : forall c in C5.permitted, T.thetaImage n c in commonHull
- hull_subset_scaleShift : commonHull ⊆ B.iqInterface.scaleShift '' B.iqInterface.unitRegion
- logVolume_lt_top : B.iqInterface.logVolume commonHull < top
- logVolume_pos : 0 < B.iqInterface.logVolume commonHull
- qPilot_mem : qPilotPoint C3 in commonHull

## 2. Exact actual obligations (C7Actual.lean)

~~~text
structure C7ActualObligations (T) (n) where
  iqHull_eq : B.iqInterface.hull = commonHull C3 mu B
  thetaImage_subset_hull : permittedImage C3 T n ⊆ commonHull C3 mu B
  qPilot_mem : qPilotPoint C3 in commonHull C3 mu B
  logVolume_pos : 0 < B.iqInterface.logVolume (commonHull C3 mu B)
~~~

No arbitrary hull is introduced. commonHull is definitionally B.hull, and B is
C6ActualIQData on the actual ArithmeticTensorTupleBlock carrier.

## 3. Proved construction

SourceHolomorphicHullData.ofObligations (O) fills every field:
- iqHull_eq, image_subset_hull, qPilot_mem, logVolume_pos: from O;
- contains_permitted: from thetaImage_subset_hull and the definition of
  permittedImage as the T.thetaImage set;
- hull_subset_scaleShift: from B.iqInterface.hull_subset_scaleShift after
  rewriting O.iqHull_eq;
- logVolume_lt_top: from IQHullLogVolumeInterface.hull_logVolume_lt_top for the
  actual interface B.iqInterface after rewriting O.iqHull_eq.

obligationsOfHull extracts the same four obligations from any hull package.

Theorem sourceHolomorphicHullData_nonempty_iff_obligations:

~~~text
Nonempty (SourceHolomorphicHullData ... T n) <->
Nonempty (C7ActualObligations T n)
~~~

The reverse direction is obligationsOfHull; the forward direction is
ofObligations. This is the exact no-go/closure statement: existence is
equivalent to the four actual obligations, not to a free hull or extra axiom.

## 4. qPilotPoint

proved:

~~~text
qPilotPoint C3 = (C3.tensorUnit : C6IQCarrier C3.tensorPlaces C3.tensorTuple)
~~~

via SourceThetaToIQ.qPilotPoint_eq_tensorUnit (actual C3 tensorLanding_q).
This does not prove tensorUnit lies in the canonical hull; that is exactly the
qPilot_mem obligation.

## 5. Exact no-go / missing actual facts

1. thetaImage containment: T.thetaImage n j = C3.tensorLanding (thetaCompletion n j).
   C3.tensorLanding is an arbitrary C3 field except tensorLanding_q; there is
   no theorem that its values lie in arithmeticTupleCanonicalHull. The T11
   thetaCompletion is itself an interface field. Hence thetaImage_subset_hull is
   not derivable from C7/C6/T11 data currently.
2. qPilot membership: C3.tensorUnit is an arbitrary unit field. No production
   theorem puts it in arithmeticTupleCanonicalHull; qPilot_mem is therefore an
   exact obligation.
3. canonical hull log-volume positivity: the interface provides only
   hull_logVolume_lt_top (finiteness). Positivity is not an interface field and
   does not follow from the measure being positive: the ENNReal Haar log-volume
   may be zero or clipped. logVolume_pos is an exact obligation; it would follow
   from an actual lower bound (for example mu hull > 1 plus a log bridge) not
   present in the current data.
4. No arbitrary hull is used: commonHull = B.hull and B is the actual
   C6ActualIQData structure. Replacing the canonical hull or adding an assumed
   source hull would change the C7 stage-2 target and is not done.

## 6. Build and status

Command:
  lake env lean -R D:/lean tmp/sheaf/n8/closure/C7Actual.lean

Result: EXIT=0; no sorry in C7Actual.lean.
Warnings: unused section variables in qPilotPoint_eq_tensorUnit; defProp
warnings for ofObligations/obligationsOfHull (they are proof-valued Prop
structures).

Status:
- statement_compiles: yes
- proof_body_checked: ofObligations, obligationsOfHull, equivalence and
  qPilotPoint_eq_tensorUnit checked by Lean.
- kernel_closed: not audited in this batch.
- target_accepted: no; zero-sorry construction is conditional on
  C7ActualObligations, and no arbitrary hull/assumption was used.

## 7. Executable next step

Prove the four obligations from actual source data, in this exact order:
1. tensorLanding/thetaCompletion integrality into arithmeticTupleCanonicalHull;
2. tensorUnit/qPilot canonical-hull membership;
3. actual positive lower bound for the canonical hull Haar log-volume.
Then sourceHolomorphicHullData_nonempty follows by
sourceHolomorphicHullData_nonempty_iff_obligations. Do not add a C7 hull
assumption or replace canonical hull.
