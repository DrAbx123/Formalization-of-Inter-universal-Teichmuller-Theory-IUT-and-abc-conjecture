# O4 constructed hull: actual theta packet and via-images identity

Date: 2026-10-24. Owner: logdescent. Lean: O4ConstructedHull.lean.
Compile: lake env lean -j1 -R D:/lean -> EXIT=0, zero sorry.

## Actual objects

- gaussianThetaPacket q hq := FiniteThetaPacket.ofQ q hq;
  gaussianThetaPacket_scale: scale j = realThetaValue q j.1;
  gaussianThetaPacket_log_scale: log scale j = gaussExponent(j)^.toNat * log q.
- sourceThetaPacket I n m := (I.theaterAt n m).thetaPacket, with scale =
  I.thetaValueAt n m j.
- possibleImageSet := I.possibleThetaPilotImageSet v R n.
- holomorphicHullActual := I.sourceHolomorphicHull v R n.
- hullVolume := I.sourceHullVolume v R n;
  imageVolume := I.sourceSetVolume v (possible theta pilot image set).
- ViaImagesIdentity := hullVolume = imageVolume.

## Actual via-images results

- viaImagesIdentity_iff_edge: ViaImagesIdentity iff hullVolume <= imageVolume
  (antisymmetric collapse using sourceHullVolume_ge_imageVolume).
- viaImagesIdentity_iff_hullLogDegree_nonpos: ViaImagesIdentity iff every hull
  point has sourceLocalLogDegree <= 0 (sharp value-layer characterization).
- not_viaImagesIdentity_of_hullLogDegree_pos: any hull point with positive
  sourceLocalLogDegree refutes ViaImagesIdentity; decisive value-layer no-go /
  actual counterexample schema.

## Boundary

The exact remaining content is the sign control of hull log-degrees (R9 /
Card-HULLREAL); the value-layer identity is now constructed and characterized
from the actual FiniteThetaPacket, possible image set, and holomorphic hull.
No arbitrary hull or readout is introduced.