import tmp.sheaf.xif.paper.S694ThetaAverageNormalizationActual
import tmp.sheaf.xif.paper.S657RootSignedHullIndependentActual

/-! # S794: paper -|log Theta| is the l* weighted procession average

Paper labels are F_l^x / ± with cardinal l* and weight 1/l* (S694).
S657/S663 uniform SignedLabel weights (card l, includes 0) are a surrogate.
This file builds the actual l*-weighted paper procession/hull and records the
exact relation to the uniform weight (l/l*). -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S794LStarProcessionAverageActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S694ThetaAverageNormalizationActual
open LeanFormal.IUT.XiFPaper.S657RootSignedHullIndependentActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Positive paper theta label i in {0,...,l*-1} maps to j=i+1. -/
def paperThetaLabelToSigned (i : PaperThetaLabel l) : SignedLabel l.value :=
  ⟨(i.1 : Int) + 1, by
    have hi := i.2
    constructor
    · have : (0 : Int) <= (i.1 : Int) := by exact_mod_cast Nat.zero_le _
      have hnn : (0 : Int) <= (lStar l.value : Int) := by exact_mod_cast Nat.zero_le _
      omega
    · have h1 : (i.1 : Int) + 1 <= (lStar l.value : Int) := by
        exact_mod_cast Nat.succ_le_of_lt hi
      exact h1⟩

/-- The actual l*-weighted paper theta procession. -/
noncomputable def paperThetaProcession : WeightedValues (PaperThetaLabel l) where
  value i := rootThetaMagnitudeValue T b (paperThetaLabelToSigned (l := l) i)
  weight _ := paperThetaLabelWeight l
  weightTotal := 1
  weightTotal_pos := by norm_num
  weightTotal_eq_sum := by
    simpa [paperThetaLabelWeight] using (paperThetaLabelWeight_sum (l := l)).symm

/-- The paper procession average equals the S694 l*-label average. -/
theorem paperThetaProcession_average_eq_label_average :
    (paperThetaProcession (l := l) T b).average =
      paperThetaLabelAverage (l := l)
        (fun i : PaperThetaLabel l =>
          rootThetaMagnitudeValue T b (paperThetaLabelToSigned (l := l) i)) := by
  unfold WeightedValues.average paperThetaProcession paperThetaLabelAverage
    paperThetaLabelWeight
  rw [div_one, Finset.mul_sum]

theorem paperThetaProcession_average_nonneg :
    0 <= (paperThetaProcession (l := l) T b).average := by
  rw [paperThetaProcession_average_eq_label_average]
  unfold paperThetaLabelAverage paperThetaLabelWeight
  apply mul_nonneg
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · apply Finset.sum_nonneg
    intro i _
    exact rootThetaMagnitudeValue_nonneg (l := l) T b _

/-- l*-label finite hull. -/
noncomputable def paperThetaFiniteHull : FiniteHull (PaperThetaLabel l) where
  volume i := (paperThetaProcession (l := l) T b).value i
  hullVolume := Finset.sum Finset.univ
    (fun i : PaperThetaLabel l => |(paperThetaProcession (l := l) T b).value i|)
  contains i := by
    calc
      (paperThetaProcession (l := l) T b).value i <=
          |(paperThetaProcession (l := l) T b).value i| := le_abs_self _
      _ <= Finset.sum Finset.univ
            (fun j : PaperThetaLabel l =>
              |(paperThetaProcession (l := l) T b).value j|) :=
        Finset.single_le_sum
          (fun j _ => abs_nonneg ((paperThetaProcession (l := l) T b).value j))
          (Finset.mem_univ i)

/-- Actual paper signed hull with l*-weights, given ambient hull normalization. -/
noncomputable def paperSignedHullLStar {X : Type*} (A : IQHullLogVolumeInterface X)
    (hnormal : A.logVolume A.hull = ENNReal.ofReal
      (paperThetaProcession (l := l) T b).average) :
    PaperSignedHull X (PaperThetaLabel l) where
  ambient := A
  procession := paperThetaProcession (l := l) T b
  hull := paperThetaFiniteHull (l := l) T b
  weighted_matches_hull := by intro i; rfl
  weights_nonnegative := by intro _; exact inv_nonneg.mpr (Nat.cast_nonneg _)
  average_nonneg := paperThetaProcession_average_nonneg (l := l) T b
  hull_logVolume_eq_average := hnormal

/-- Correct paper weight relation: paper l* weight / uniform SignedLabel = l/l*. -/
theorem paperWeight_eq_ratio_uniform :
    paperThetaLabelWeight l =
      (l.value : Real) / (lStar l.value : Real) * uniformSignedLabelWeight l :=
  paperThetaLabelWeight_eq_ratio l

end LeanFormal.IUT.XiFPaper.S794LStarProcessionAverageActual

end
