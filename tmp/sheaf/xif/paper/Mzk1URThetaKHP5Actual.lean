/- U-R C2 hP5 (P) K-side (kurt), first batch: label-1 inclusion, ceiling comparison,
and the M_paper <= M_paperCeil relation (no new objects, no conditions).

* the label-1 theta region lies in the nonzero-label theta hull closure;
* actualRootCoeff = c_norm/(2l) <= urCeilC (value-group ceiling);
* M_paper (paper |log q| = Q_paper/(2l)) <= M_paperCeil (integral-valuation form).

The exact hull-level chain available is -M_paperCeil <= ksThetaHullLogRoot (next
batch with the normalized-log-volume monotonicity).

Default heartbeats (heartbeat-cleanup batch). -/
import tmp.sheaf.xif.paper.Mzk1URThetaKLowerActual
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import tmp.sheaf.xif.paper.Mzk1URThetaHullTensorActual
import tmp.sheaf.xif.paper.Mzk1URQAllParamActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaKHP5Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerActual
open LeanFormal.IUT.XiFPaper.Mzk1URQAllParamActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaHullUpperActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open MeasureTheory

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (ksBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (ksBlock T b)]

/-- The label-1 theta region lies in the nonzero-label theta hull. -/
theorem ksOneLabelRegion_subset_hull (b : Bad (nativePlaceSelection T)) :
    ksThetaRegion (l := l) T b (oneLabel l) ⊆ ksThetaHull (l := l) T b := by
  unfold ksThetaHull
  intro x hx
  exact subset_closure (s := ksThetaImageSet (l := l) T b)
    (Set.mem_iUnion.mpr ⟨⟨oneLabel l, by show (oneLabel l).1 ≠ 0; simp [oneLabel]⟩, hx⟩)

/-- The half root coefficient is at most its value-group ceiling. -/
theorem ksRootCoeff_le_urCeilC (b : Bad (nativePlaceSelection T)) :
    actualRootCoeff T b () ≤ urCeilC T b := by
  rw [urCeilC_eq T b]
  unfold ksCeilCoeff
  exact le_ceilExp (p := (completionRationalPrime (nativeBadToKPlace T b)).val)
    (K := CommonPrimeCompletion (ksPlace T b)) (urRootCoeff_nonneg' T b)

/-- The integral-valuation (ceiling) version of M_paper. -/
noncomputable def M_paperCeil : ℝ :=
  ∑ b : Bad (nativePlaceSelection T),
    normDegreeWeight T b * (urCeilC (l := l) T b * ksLogP T b)

/-- M_paper rewritten as the weighted sum of the real half-root coefficients. -/
theorem M_paper_eq_sum_actualRootCoeff :
    M_paper (l := l) T =
      ∑ b : Bad (nativePlaceSelection T),
        normDegreeWeight T b * (actualRootCoeff (l := l) T b () * ksLogP T b) := by
  unfold M_paper qPilotMagnitudePaper actualRootCoeff
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun b _ => by ring)

/-- The paper M_paper is at most its integral-valuation normalization. -/
theorem M_paper_le_M_paperCeil : M_paper (l := l) T ≤ M_paperCeil (l := l) T := by
  rw [M_paper_eq_sum_actualRootCoeff]
  unfold M_paperCeil
  exact Finset.sum_le_sum (fun b _ =>
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (ksRootCoeff_le_urCeilC T b)
        (ksLogP_nonneg T b))
      (normDegreeWeight_nonneg (l := l) T b))


#print axioms ksOneLabelRegion_subset_hull
#print axioms ksRootCoeff_le_urCeilC
#print axioms M_paper_eq_sum_actualRootCoeff
#print axioms M_paper_le_M_paperCeil

end LeanFormal.IUT.XiFPaper.Mzk1URThetaKHP5Actual
end