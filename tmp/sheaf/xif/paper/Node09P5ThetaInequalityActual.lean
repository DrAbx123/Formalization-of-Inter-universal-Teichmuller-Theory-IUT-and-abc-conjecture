import tmp.sheaf.xif.paper.GlobalQVFamThetaHullScalarActual
import tmp.sheaf.xif.paper.Node09H1bTensorVolumeActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullScalarActual

namespace LeanFormal.IUT.XiFPaper.Node09P5ThetaInequalityActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (QFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (QFamTensorBlock T b)]

/-- Actual P5 local-to-global theta inequality: from the actual per-b region
inclusion and the actual normalized-log-volume monotonicity, the qVFam q-pilot
global scalar is at most the theta-hull global scalar. -/
theorem p5_qVFamQPilotLog_le_thetaHull
    (hpos : ∀ b : Bad (nativePlaceSelection T),
      0 < MeasureTheory.Measure.addHaar (qVFamLocalQPilotRegion T b))
    (hfin : ∀ b : Bad (nativePlaceSelection T),
      MeasureTheory.Measure.addHaar (qVFamLocalThetaHull T b) < ⊤) :
    globalQVFamQPilotLog T ≤ globalQVFamThetaHullLog T :=
  globalQVFamQPilotLog_le_thetaHull T
    (fun b => qVFamLocalQPilotLogVolume_le_thetaHull T b (hpos b) (hfin b))

def Node09P5ThetaInequalityStatus : List String :=
  [ "actual DONE: p5_qVFamQPilotLog_le_thetaHull proves globalQVFamQPilotLog <= globalQVFamThetaHullLog from the actual per-b qVFamLocalQPilotRegion_subset_thetaHull plus arithmeticTupleNormalizedLogVolume_mono",
    "actual donor: GlobalQVFamThetaHullScalarActual.qVFamLocalQPilotRegion_subset_thetaHull and qVFamLocalQPilotLogVolume_le_thetaHull",
    "TRUE BLOCKER 1: no producer for the actual per-b measures hpos : 0 < addHaar (qVFamLocalQPilotRegion) and hfin : addHaar (qVFamLocalThetaHull) < top; the region/hull compactness and positive-mass lemmas for these qVFam scaled regions are absent",
    "TRUE BLOCKER 2: no producer identifies the P4 Jq/qReading scalar qPilotRealifiedLogVolume or weightedReadout with globalQVFamQPilotLog; S1113ConcreteFinalScalarBridgeActual.S1113QPilotScalarIdentification is exactly this missing bridge",
    "TRUE BLOCKER 3: the H1b tensor signed volume arithmeticTupleLogTensorUnitLogVolume is a relative integral-log-lattice volume, not identified with globalQVFamThetaHullLog; no inclusion/certificate lemma connects them",
    "no fake, no True/PUnit/axiom/sorry" ]

end LeanFormal.IUT.XiFPaper.Node09P5ThetaInequalityActual