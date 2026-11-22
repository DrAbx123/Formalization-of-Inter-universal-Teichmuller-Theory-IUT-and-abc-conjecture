/- PREREQ C: actual F-side packet value packetV and its per-b hstepVIII/upper bound.
   packetV b := actualLocalHullLog b (the actual F-side local hull log; NOT K-side).
   Under the DONE actual root-hull scaling formula RootHullScalingFormulaAt:
     packetV b = -(c_norm_b/(2l)) * log p_b,
   hence sum_b nativeBadLocalWeight_b * packetV_b = -(1/(2l)) * actualQPilotMagnitudeClassical.
   The C4 fside hstepVIII then follows from the single scalar bound on the RHS bracket. -/
import tmp.sheaf.xif.paper.BadPlaceThetaHullCorrectionFormulaActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.FsidePacketVActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.BadPlaceThetaHullCorrectionFormulaActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- The actual F-side q-packet value at b: the local hull log. -/
noncomputable def packetV (b : Bad (nativePlaceSelection T)) : Real :=
  actualLocalHullLog (l := l) T b

/-- Per-b hperB (F-side hull <= packetV), with packetV the actual hull log. -/
theorem hperB_packetV (b : Bad (nativePlaceSelection T)) :
    actualLocalHullLog (l := l) T b <= packetV (l := l) T b :=
  le_refl _

/-- Per-b packet value in the paper half coefficient form. -/
theorem packetV_eq_neg_halfCoefficient
    (h : ∀ b : Bad (nativePlaceSelection T), RootHullScalingFormulaAt (l := l) T b)
    (b : Bad (nativePlaceSelection T)) :
    packetV (l := l) T b =
      - (QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b /
          (2 * (l.value : Real))) * Real.log (qVFamTensorP T b : Real) := by
  unfold packetV
  rw [h b]
  unfold thetaCoefficientContribution
  ring

/-- Sum identity needed by the F-side C4 hstepVIII. -/
theorem sum_native_weight_packetV_eq
    (h : ∀ b : Bad (nativePlaceSelection T), RootHullScalingFormulaAt (l := l) T b) :
    (∑ b : Bad (nativePlaceSelection T), nativeBadLocalWeight T b * packetV (l := l) T b) =
      - (1 / (2 * (l.value : Real))) * actualQPilotMagnitudeClassical (l := l) T := by
  unfold actualQPilotMagnitudeClassical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [packetV_eq_neg_halfCoefficient (l := l) T h b]
  ring

/-- Pre-C4 hstepVIII for packetV: reduces to the single scalar bound on the RHS. -/
theorem hstepVIII_packetV_of_bound
    (h : ∀ b : Bad (nativePlaceSelection T), RootHullScalingFormulaAt (l := l) T b)
    (rhs : Real)
    (hmain : - (1 / (2 * (l.value : Real))) * actualQPilotMagnitudeClassical (l := l) T
      <= rhs - actualQPilotMagnitudeClassical (l := l) T) :
    (∑ b : Bad (nativePlaceSelection T), nativeBadLocalWeight T b * packetV (l := l) T b)
      <= rhs - actualQPilotMagnitudeClassical (l := l) T := by
  rw [sum_native_weight_packetV_eq (l := l) T h]
  exact hmain

#print axioms hperB_packetV
#print axioms packetV_eq_neg_halfCoefficient
#print axioms sum_native_weight_packetV_eq
#print axioms hstepVIII_packetV_of_bound

end LeanFormal.IUT.XiFPaper.FsidePacketVActual
