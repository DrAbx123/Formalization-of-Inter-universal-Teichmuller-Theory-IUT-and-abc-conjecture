/- R2 upper: transfer hread (readout) to hH (perBThetaHullLog) by the DONE per-b identity.

`Mzk1G1R1IR2PaperThetaRowReadoutActual.paperThetaReadoutB_eq_perBThetaHullLog` (DONE trio)
says paperThetaReadoutB = perBThetaHullLog per b.  Hence the weighted sum is identical, so
the missing R2 input hH is exactly the weighted readout bound (hread) with the same H.
-/
import tmp.sheaf.xif.paper.Mzk1G1R1IR2PaperThetaRowReadoutActual
import Mathlib.Tactic
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2R2HreadTransferActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1G1R1IR2PaperThetaRowReadoutActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- The R2 hH input is exactly the weighted paper-Theta readout bound hread. -/
theorem hH_iff_hread (H : Real) (w : Bad (nativePlaceSelection T) → Real) :
    (∑ b : Bad (nativePlaceSelection T), w b *
        LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual.perBThetaHullLog (l := l) (T := T) b) ≤ H ↔
      (∑ b : Bad (nativePlaceSelection T), w b *
        LeanFormal.IUT.XiFPaper.Mzk1BoxR2PaperThetaLeHActual.paperThetaReadoutB (l := l) (T := T) b) ≤ H := by
  congr 2 with b
  exact (paperThetaReadoutB_eq_perBThetaHullLog (l := l) (T := T) b).symm

#print axioms hH_iff_hread
end LeanFormal.IUT.XiFPaper.Mzk1G1F2R2HreadTransferActual