# GEOM-SIMPLIFICATIONS (A1128)

Status: read-only; no compile.

## 1. tensorRegionHull

S971:55-59: tensorRegionHull D = closure (tensorThetaRegionIndUnion T b) with
D.topologicalSpace. The paper/lana holomorphic hull is the least a.O region
containing the possible images (leastLambdaOHull / LocalTheory.leastHull).
A topological closure is not, in general, the least a.O region; no theorem
identifies them. FinalLValuedCarrier has no canonical locally compact topology,
so D.topologicalSpace is an arbitrary field. Hence tensorRegionHull is a
closure surrogate and a model simplification.

## 2. unitRegion in S994/S1004

S994:54-55 s994H = finiteLogShellHaarData p L.d.
S1004:62-64 s1004H = finiteLogShellHaarData p d.
S976:36-48: measure = Measure.addHaar on Fin d -> Qp; unitRegion =
Metric.closedBall 0 1; unit_pos, unit_lt_top proved. So S994/S1004 use the
actual finite closed unit ball and actual addHaar, not an arbitrary region.
But this is on the finite coordinate carrier after a linearization; the full
FinalLTensorLogVolumeData (S956) still has arbitrary measure/unitRegion fields.

## 3. qPilotPaperImageInLValued

S945:68: qPilotPaperImageInLValued = qVFamToLValued '' qPilotPaperRegion.
qPilotPaperRegion (S778:48, S800:76) = thetaTensorScaledRegion at
rootHalfCoefficient T b, and S778:52 identifies it with the j=1 root theta
region at coefficient order/(2l). lana qRegion (QPilotRegion:314) = pow D
(fun _ => 1) (labOne D) (integralRegion D), the j=1 theta value in every
capsule at label 1. These are model definitions at the same j=1 coefficient,
but no theorem identifies qPilotPaperRegion with lana qRegion or with the paper
q-pilot. qVFamToLValued x = x tensor 1 is not measure/topology preserving
(no theorem). Hence qPilotPaperImageInLValued is a model image.

## 4. Consequences

The green chain qPilotPaperImageInLValued subset tensorRegionHull (S971:61)
=> qPilotTensorLog <= tensorRegionHullLog (S979:59) is real on the model
carrier, but the hull is a closure surrogate, the normalization is finite
addHaar + closed ball on Fin d -> Qp, not C3, and the qPilot image is a j=1
root-theta model image. It cannot be read as the paper q <= Theta statement
without three identifications: closure to least hull, finite carrier to FinalL
carrier, model qPilot to paper/lana qPilot. All are GAPs.

## 5. Verdict

- tensorRegionHull: model simplification (closure, arbitrary topology).
- unitRegion in S994/S1004: actual finite closed ball/addHaar after
  linearization; full carrier data remains arbitrary.
- qPilotPaperImageInLValued: model j=1 root-theta image, not identified with
  paper/lana q-pilot.
- Green chain is conditional/model-level; no fake identification.
