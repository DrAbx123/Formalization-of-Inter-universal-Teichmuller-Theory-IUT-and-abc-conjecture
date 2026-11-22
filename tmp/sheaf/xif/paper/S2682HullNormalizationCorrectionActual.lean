import tmp.sheaf.xif.paper.BaseQLogVolumeActual
import tmp.sheaf.xif.paper.BaseQFamilyActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2682HullNormalizationCorrectionActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The native base-q (bad-prime) correction term of the hull normalization. -/
noncomputable def S2682BadQCorrection
    [Fintype (Bad (nativePlaceSelection T))] : Real :=
  baseQTotalLogMagnitude T

/-- Corrected hull normalization: paper signed-average normalization plus the
native bad-prime base-q term.  This is the object missing from the concrete
hull, whose normalization fixed only the Gaussian theta average. -/
noncomputable def S2682CorrectedHullNormalization
    (baseNormalization : Real) [Fintype (Bad (nativePlaceSelection T))] : Real :=
  baseNormalization + S2682BadQCorrection T

theorem S2682Corrected_ge_base
    (baseNormalization : Real) [Fintype (Bad (nativePlaceSelection T))]
    (hbase : 0 <= baseNormalization) :
    baseNormalization <= S2682CorrectedHullNormalization T baseNormalization :=
  by
    unfold S2682CorrectedHullNormalization S2682BadQCorrection
    have hnonneg : 0 <= baseQTotalLogMagnitude T := by
      unfold baseQTotalLogMagnitude
      exact Finset.sum_nonneg (fun b _ => le_of_lt (baseQLogMagnitude_pos T b))
    linarith

theorem S2682BadQCorrection_eq_zero_of_isEmpty
    [Fintype (Bad (nativePlaceSelection T))]
    [IsEmpty (Bad (nativePlaceSelection T))] :
    S2682BadQCorrection T = 0 := by
  unfold S2682BadQCorrection baseQTotalLogMagnitude
  simp

/-- Exact obstruction: the uncorrected concrete hull normalization cannot
dominate a positive paper Gaussian term when the bad-prime set is empty. -/
theorem S2682UncorrectedEmptyBadSetObstruction
    (baseNormalization : Real) (hpos : 0 < baseNormalization)
    [Fintype (Bad (nativePlaceSelection T))]
    [IsEmpty (Bad (nativePlaceSelection T))] :
    baseNormalization <= S2682BadQCorrection T -> False := by
  intro h
  rw [S2682BadQCorrection_eq_zero_of_isEmpty T] at h
  linarith

theorem S2682TwoLog5_le_corrected
    [Fintype (Bad (nativePlaceSelection T))] :
    (2 : Real) * Real.log 5 <= S2682CorrectedHullNormalization T (2 * Real.log 5) := by
  refine S2682Corrected_ge_base T (2 * Real.log 5) ?_
  have h5 : (0 : Real) < 5 := by norm_num
  exact mul_nonneg (by norm_num) (le_of_lt (Real.log_pos (by norm_num)))

theorem S2682TwoLog5_not_le_badQ_of_isEmpty
    [Fintype (Bad (nativePlaceSelection T))]
    [IsEmpty (Bad (nativePlaceSelection T))] :
    ¬ ((2 : Real) * Real.log 5 <= S2682BadQCorrection T) :=
  S2682UncorrectedEmptyBadSetObstruction T (2 * Real.log 5) (by
    have h5 : (1 : Real) < 5 := by norm_num
    exact mul_pos (by norm_num) (Real.log_pos h5))

#check S2682BadQCorrection
#check S2682CorrectedHullNormalization
#check S2682Corrected_ge_base
#check S2682BadQCorrection_eq_zero_of_isEmpty
#check S2682UncorrectedEmptyBadSetObstruction
#print axioms S2682Corrected_ge_base
#print axioms S2682UncorrectedEmptyBadSetObstruction
end LeanFormal.IUT.XiFPaper.S2682HullNormalizationCorrectionActual
end