namespace LeanFormal.IUT.XiFPaper.Node09P5ThetaReadingActual

/-- P5 theta-side reading status after the H1b/actual-table attempt.
This is a documentation record; no inequality or equality is assumed. -/
def Node09P5ThetaReadingStatus : List String :=
  [ "actual available: Mzk1P5ActualPacketTable.finiteSourceImage = actual tensor log-shell product image; unitReferenceLattice = actual C_t; gammaP5 = integral span; HP5 = holomorphic hull",
    "actual available: Node09H1bTensorVolumeActual.h1b_signed_volume_actual and h1b_signed_volume_eq_relativeHaarLog give the arithmetic tensor signed log-volume = relative Haar log form",
    "actual available: Node09H1bVolumeActual.vP5 = residueDegree * rP5 * log p is the combined H1b signed density",
    "actual available: Mzk1P4P5QThetaReadingIntegrationActual.p5_actualQReadingInput gives the P4 qPilotRealifiedLogVolume = weightedReadout q-reading",
    "TRUE BLOCKER: no producer of actualNormalizedLogVolume (gammaP5 finiteSourceImage) C_t μ = productLocalLogSum / qReading. Mzk1P5MeasureLogBridgeActual.actualNormalizedLogVolume_eq_productLocalLogSum has this as an explicit hypothesis; Mzk1P5OTVolumeActual.actualNormalizedLogVolume_eq_qReading_of_bridges needs ProductHaarToFiberMult + WeightedQSumBridge; Mzk1ProductFiberMultBridgeGapActual.ProductHaarToFiberMult and ClosedBallMassFormula have no producers",
    "the H1b signed/relative Haar forms are not an actual closed-ball/product Haar mass formula for gammaP5, so they do not identify the measured Gamma_t volume with qReading",
    "no fake, no True/PUnit/axiom/sorry" ]

end LeanFormal.IUT.XiFPaper.Node09P5ThetaReadingActual