/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PaperFaithfulHullActual
import tmp.sheaf.xif.paper.S920SHullFinitenessActual
import tmp.sheaf.xif.paper.S779RootHullNonzeroFixActual
import tmp.sheaf.xif.paper.S806PaperRootHullNonzeroGapsActual
import tmp.sheaf.xif.paper.S1023FractionalLatticeOpenActual
import tmp.sheaf.xif.paper.S923RInteriorNonemptyActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientActual
import tmp.sheaf.xif.paper.ThetaTensorScaledImageActual
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual
import Mathlib.Tactic

/-! # P4 for the paper-faithful Theta hull (positivity + finiteness)

| field | value |
|---|---|---|
| Status | P4: finiteness via S920 nonzero hull, positivity via S1023 openness of F(c_root). |
| GAP | coefficient bridge qVFamPaperRootCoefficient = rootHalfCoefficient is avoided, not used. |
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperFaithfulHullP4Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1PaperFaithfulHullActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.XiFPaper.S920SHullFinitenessActual
open LeanFormal.IUT.XiFPaper.S779RootHullNonzeroFixActual
open LeanFormal.IUT.XiFPaper.S806PaperRootHullNonzeroGapsActual
open LeanFormal.IUT.XiFPaper.S1023FractionalLatticeOpenActual
open LeanFormal.IUT.XiFPaper.S923RInteriorNonemptyActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open MeasureTheory
open scoped Pointwise

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b' : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b')]
variable [∀ b' : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b')]
variable (mu : Measure (qVFamTensorBlock T b))
variable [Measure.IsAddHaarMeasure mu]

theorem paperFaithfulThetaHull_eq_nonzeroHull :
    paperFaithfulThetaHull (l := l) T b =
      S806PaperRootHullNonzeroGapsActual.paperRootThetaHullNonzero (l := l) T b := by
  unfold paperFaithfulThetaHull S806PaperRootHullNonzeroGapsActual.paperRootThetaHullNonzero
  congr 1

theorem paperFaithfulThetaHull_measure_lt_top :
    mu (paperFaithfulThetaHull (l := l) T b) < ⊤ := by
  rw [paperFaithfulThetaHull_eq_nonzeroHull]
  have hsub : S806PaperRootHullNonzeroGapsActual.paperRootThetaHullNonzero (l := l) T b ⊆ s920O (l := l) T b := by
    unfold S806PaperRootHullNonzeroGapsActual.paperRootThetaHullNonzero
    apply closure_minimal
    · intro y hy
      rcases Set.mem_iUnion.mp hy with ⟨j, hj⟩
      exact s920PaperRegion_subset_O (l := l) T b j.1 hj
    · exact (isCompact_arithmeticTupleCanonicalRegions
        (qVFamTensorPlaces T b) qVFamTensorTuple).2.isClosed
  exact lt_of_le_of_lt (measure_mono hsub)
    (isCompact_arithmeticTupleCanonicalRegions
      (qVFamTensorPlaces T b) qVFamTensorTuple).2.measure_lt_top

theorem fractional_lattice_open :
    IsOpen (arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
      qVFamTensorTuple (paperRootCoefficientFamily (l := l) T b) :
        Set (qVFamTensorBlock T b)) := by
  have h := s923FractionalLatticeOpen_actual T b
  unfold S923FractionalLatticeOpen s923F at h
  simpa [paperRootCoefficientFamily] using h

theorem fractional_subset_scaled :
    (arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
      qVFamTensorTuple (paperRootCoefficientFamily (l := l) T b) :
        Set (qVFamTensorBlock T b)) ⊆
      thetaTensorScaledRegion (qVFamTensorPlaces T b) qVFamTensorTuple
        (paperRootCoefficientFamily (l := l) T b) := by
  intro x hx
  unfold thetaTensorScaledRegion
  have h1 : (1 : qVFamTensorBlock T b) ∈
      arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple := by
    change IsIntegral ℤ_[(qVFamTensorP T b)] (1 : qVFamTensorBlock T b)
    exact isIntegral_one
  have hm := Submodule.mul_mem_mul hx h1
  change x ∈ (arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
    qVFamTensorTuple (paperRootCoefficientFamily (l := l) T b) *
    arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :
      Submodule ℤ_[(qVFamTensorP T b)] (qVFamTensorBlock T b))
  simpa only [mul_one] using hm

theorem scaledRegion_subset_paperHull :
    thetaTensorScaledRegion (qVFamTensorPlaces T b) qVFamTensorTuple
      (paperRootCoefficientFamily (l := l) T b) ⊆
      paperFaithfulThetaHull (l := l) T b := by
  rw [paperFaithfulThetaHull]
  have himg : paperFaithfulThetaImage (l := l) T b =
      thetaTensorScaledRegion (qVFamTensorPlaces T b) qVFamTensorTuple
        (paperRootCoefficientFamily (l := l) T b) := by
    rw [paperFaithfulThetaImage_eq_scaledRegion]
    rfl
  rw [← himg]
  exact subset_closure

theorem paperFaithfulThetaHull_measure_pos :
    0 < mu (paperFaithfulThetaHull (l := l) T b) := by
  have hpos : 0 < mu (arithmeticTupleFractionalLattice
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (paperRootCoefficientFamily (l := l) T b) :
        Set (qVFamTensorBlock T b)) :=
    (fractional_lattice_open (l := l) T b).measure_pos mu
      ⟨0, Submodule.zero_mem _⟩
  exact lt_of_lt_of_le hpos (measure_mono (by
    intro x hx
    exact scaledRegion_subset_paperHull (l := l) T b
      (fractional_subset_scaled (l := l) T b hx)))

def rows : List (String × String × String) :=
  [ ("paperFaithfulThetaHull_measure_lt_top", "finite", "PROVED"),
    ("paperFaithfulThetaHull_measure_pos", "positive", "PROVED"),
    ("coefficient bridge", "not used", "AVOIDED") ]

theorem rows_length : rows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1PaperFaithfulHullP4Actual

end