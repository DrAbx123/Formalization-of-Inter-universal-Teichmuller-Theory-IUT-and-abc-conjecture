/- R2 row-readout identification (easy direction, one-way): the paper Theta row readout
`Mzk1BoxR2PaperThetaLeHActual.paperThetaReadoutB` is the S716 per-b paper hull log
`PaperLevelXiFTargetProofActual.perBThetaHullLog` (both definitionally the normalized
log-volume of `rootNormHull`; `S716...:54,57` are `rfl` lemmas).
EXACT MISSING TRANSFER (not assumed): `packetHull (D t)` volume vs `rootNormHull` volume;
the packet-hull carrier is `ArithmeticTensorTupleBlock places tuple` while the readout's is
`qVFamTensorBlock T b`, and only `ksThetaHull_subset_packetHull_actual` exists (ks block).
No fake; no equality with packet hull claimed. -/
import tmp.sheaf.xif.paper.Mzk1BoxR2PaperThetaLeHActual
import tmp.sheaf.xif.paper.S716PaperThetaHullLogSourceAuditActual
import Mathlib.Tactic

set_option maxHeartbeats 4000000

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1R1IR2PaperThetaRowReadoutActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- The R2 paper-Theta row readout is the S716 per-b paper hull log. -/
theorem paperThetaReadoutB_eq_perBThetaHullLog (b : Bad (nativePlaceSelection T)) :
    LeanFormal.IUT.XiFPaper.Mzk1BoxR2PaperThetaLeHActual.paperThetaReadoutB (l := l) (T := T) b =
      LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual.perBThetaHullLog (l := l) (T := T) b := by
  unfold LeanFormal.IUT.XiFPaper.Mzk1BoxR2PaperThetaLeHActual.paperThetaReadoutB
  exact (LeanFormal.IUT.XiFPaper.S716PaperThetaHullLogSourceAuditActual.paperPerBThetaHullLog_eq_ambientHullLog
      (l := l) T b).symm.trans rfl

#print axioms paperThetaReadoutB_eq_perBThetaHullLog
end LeanFormal.IUT.XiFPaper.Mzk1G1R1IR2PaperThetaRowReadoutActual