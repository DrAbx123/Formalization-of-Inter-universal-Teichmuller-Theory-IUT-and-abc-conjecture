import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual
import tmp.sheaf.xif.paper.SignedLabelOneActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual

-- S793: paper hull is the LEAST lambda*O region containing the image
-- (intersection of candidates), not closure(union_j F(j^2 c)O).
-- Actual candidate family and least hull; old union hull is only a
-- superset, with exact reverse-closure gap.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

abbrev PaperLabel := SignedLabel l.value
abbrev PaperNonzeroLabel := {j : PaperLabel (l := l) // j.1 ≠ 0}

theorem paperRootCoefficientFamily_nonneg_local (i : qVFamTensorV) :
    0 ≤ paperRootCoefficientFamily T b i := by
  unfold paperRootCoefficientFamily qVFamPaperRootCoefficient
  positivity

theorem paperOneLabel_ne_zero : (oneLabel l).1 ≠ 0 := by
  intro hzero
  have h := gaussExponent_oneLabel l
  rw [hzero] at h
  norm_num [gaussExponent] at h

theorem one_le_gaussExponent_of_ne_zero {j : PaperLabel (l := l)}
    (hj : j.1 ≠ 0) : 1 ≤ (gaussExponent j.1).toNat := by
  have hpos : 0 < j.1 ^ 2 := sq_pos_of_ne_zero hj
  have hcast : ((j.1 ^ 2).toNat : Int) = j.1 ^ 2 := Int.toNat_of_nonneg hpos.le
  unfold gaussExponent
  omega

/-- Fractional-lattice lambda*O region with exponent vector lambda. -/
noncomputable def paperLambdaORegion (lam : qVFamTensorV → Real) :
    Set (qVFamTensorBlock T b) :=
  ((arithmeticTupleFractionalLattice (qVFamTensorPlaces T b) qVFamTensorTuple lam *
    arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :
      Submodule ℤ_[qVFamTensorP T b] (qVFamTensorBlock T b)) :
    Set (qVFamTensorBlock T b))

/-- Paper image set at nonzero labels, per label j. -/
noncomputable def paperRootThetaRegionNZ (j : PaperNonzeroLabel (l := l)) :
    Set (qVFamTensorBlock T b) :=
  paperLambdaORegion (l := l) T b
    (fun i => ((gaussExponent j.1.1).toNat : Real) *
      paperRootCoefficientFamily T b i)

noncomputable def paperRootThetaImageNZ : Set (qVFamTensorBlock T b) :=
  ⋃ j : PaperNonzeroLabel (l := l), paperRootThetaRegionNZ (l := l) T b j

/-- Candidate lambda*O hulls containing the image. -/
noncomputable def paperLambdaOCandidates :
    Set (Set (qVFamTensorBlock T b)) :=
  {H | ∃ lam : qVFamTensorV → Real,
      (∀ i, paperRootCoefficientFamily T b i ≤ lam i) ∧
      H = paperLambdaORegion (l := l) T b lam ∧
      paperRootThetaImageNZ (l := l) T b ⊆ H}

/-- Literal least lambda*O hull: intersection of all candidates. -/
noncomputable def paperLeastLambdaOHull : Set (qVFamTensorBlock T b) :=
  ⋂ H ∈ paperLambdaOCandidates (l := l) T b, H

theorem paperRootThetaImageNZ_subset_minimal :
    paperRootThetaImageNZ (l := l) T b ⊆
      paperLambdaORegion (l := l) T b (paperRootCoefficientFamily T b) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
  unfold paperRootThetaRegionNZ at hj
  have hexp : (1 : Real) ≤ ((gaussExponent j.1.1).toNat : Real) := by
    exact_mod_cast one_le_gaussExponent_of_ne_zero (l := l) j.2
  have hcoeff : ∀ i, paperRootCoefficientFamily T b i ≤
      ((gaussExponent j.1.1).toNat : Real) * paperRootCoefficientFamily T b i := by
    intro i
    calc paperRootCoefficientFamily T b i = 1 * paperRootCoefficientFamily T b i := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hexp
        (paperRootCoefficientFamily_nonneg_local (l := l) T b i)
  have hlat : arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
      qVFamTensorTuple (fun i => ((gaussExponent j.1.1).toNat : Real) *
        paperRootCoefficientFamily T b i) ≤
      arithmeticTupleFractionalLattice (qVFamTensorPlaces T b) qVFamTensorTuple
        (paperRootCoefficientFamily T b) := by
    apply arithmeticTupleFractionalLattice_mono
    intro i
    simpa using hcoeff i
  exact (mul_le_mul' hlat le_rfl) hj

theorem paperLambdaORegion_cRoot_mem_candidates :
    paperLambdaORegion (l := l) T b (paperRootCoefficientFamily T b) ∈
      paperLambdaOCandidates (l := l) T b := by
  refine ⟨paperRootCoefficientFamily T b, (fun _ => le_rfl), rfl, ?_⟩
  exact paperRootThetaImageNZ_subset_minimal (l := l) T b

theorem paperLeastLambdaOHull_subset_cRoot :
    paperLeastLambdaOHull (l := l) T b ⊆
      paperLambdaORegion (l := l) T b (paperRootCoefficientFamily T b) := by
  intro x hx
  unfold paperLeastLambdaOHull at hx
  simp only [Set.mem_iInter] at hx
  exact hx _ (paperLambdaORegion_cRoot_mem_candidates (l := l) T b)

theorem paperLambdaORegion_cRoot_subset_least :
    paperLambdaORegion (l := l) T b (paperRootCoefficientFamily T b) ⊆
      paperLeastLambdaOHull (l := l) T b := by
  intro x hx
  unfold paperLeastLambdaOHull
  simp only [Set.mem_iInter]
  intro H hH
  rcases hH with ⟨lam, hle, rfl, himage⟩
  apply himage
  apply Set.mem_iUnion.mpr
  refine ⟨⟨oneLabel l, paperOneLabel_ne_zero (l := l)⟩, ?_⟩
  change x ∈ paperLambdaORegion (l := l) T b
    (fun i => ((gaussExponent (oneLabel l).1).toNat : Real) *
      paperRootCoefficientFamily T b i)
  rw [gaussExponent_oneLabel]
  simpa [paperLambdaORegion, one_mul] using hx

theorem paperLeastLambdaOHull_eq_minimal :
    paperLeastLambdaOHull (l := l) T b =
      paperLambdaORegion (l := l) T b (paperRootCoefficientFamily T b) :=
  Set.Subset.antisymm (paperLeastLambdaOHull_subset_cRoot (l := l) T b)
    (paperLambdaORegion_cRoot_subset_least (l := l) T b)

/-- Old union-closure hull is a superset of the true least lambda-O hull. -/
theorem paperLeastLambdaOHull_subset_old_unionHull :
    paperLeastLambdaOHull (l := l) T b ⊆ paperRootThetaHull T b := by
  rw [paperLeastLambdaOHull_eq_minimal (l := l) T b]
  intro x hx
  unfold paperRootThetaHull rootThetaHull rootThetaImageSet
  apply subset_closure
  apply Set.mem_iUnion.mpr
  refine ⟨oneLabel l, ?_⟩
  unfold rootThetaRegion
  rw [gaussExponent_oneLabel]
  simpa [paperLambdaORegion] using hx

/-- Exact reverse gap: the old union/closure hull is the least hull only if
closure adds nothing. -/
def OldUnionEqualsLeastLambdaOHull : Prop :=
  paperRootThetaHull T b = paperLeastLambdaOHull (l := l) T b

#check paperLeastLambdaOHull
#check paperLeastLambdaOHull_eq_minimal
#check paperLeastLambdaOHull_subset_old_unionHull
#check OldUnionEqualsLeastLambdaOHull

end LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual

end