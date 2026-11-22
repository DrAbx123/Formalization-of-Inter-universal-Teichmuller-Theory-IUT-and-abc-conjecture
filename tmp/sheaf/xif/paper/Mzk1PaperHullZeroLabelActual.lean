/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S800LeastLambdaOHullActual
import tmp.sheaf.xif.paper.Mzk1PaperBlockTargetActual
import tmp.sheaf.xif.paper.RootHullMeasureActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceLabelWeightedDiagonal
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIntegralTensorCovolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import Mathlib.Tactic

/-! # j=0 contamination of S800 paperHullLog

This audit is **not a first discovery**: the zero-label machinery and old-hull containment were
already present in `S779RootHullNonzeroFixActual` (`zeroSignedLabel` :159, NonzeroLabel :48,
`rootThetaImageSetNonzero`/`rootThetaHullNonzero` :58-64, `zero_region_subset_old_paperRootThetaHull` :204-212),
and S793 records the old/nonzero hull naming GAP as `OldUnionEqualsLeastLambdaOHull` :170-171.
This file only records the concrete S800 consequence: because S800's `paperPossibleImages` is
`rootThetaImageSet` over all SignedLabel (including j=0), its least hull contains and is equal to the
j=0 region F(0)O = R*O = O_hol, hence `paperHullLog = 0`.

S800 `paperPossibleImages` uses `rootThetaImageSet` over all SignedLabel (including j=0).
At j=0, rootThetaRegion = F(0)*O_hol = R*O_hol = O_hol. Since every candidate hull containing
the possible images must contain this j=0 term, the least hull contains O_hol; conversely
lambdaORegion 0 = O_hol is itself a candidate, so the least hull is exactly O_hol and
`paperHullLog = 0`. Thus S800's paperHullLog is q-order independent and the unconditional
paperTargetNormalization is weakened by the j=0 term, not the paper q^{j^2} comparison.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperHullZeroLabelActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S800LeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullMeasureActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperBlockTargetActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]
variable (mu : Measure (qVFamTensorBlock T b))
variable [Measure.IsAddHaarMeasure mu]

abbrev zeroLabel (l : PrimeGeFive) : SignedLabel l.value :=
  LeanFormal.IUT.SourceLabelWeightedDiagonal.zeroLabel (l := l.value)

abbrev RmulO : Set (qVFamTensorBlock T b) :=
  ((arithmeticTupleValuationIntegerLattice (qVFamTensorPlaces T b)
      qVFamTensorTuple * arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b)
        qVFamTensorTuple : Submodule ℤ_[(qVFamTensorP T b)] (qVFamTensorBlock T b)) :
    Set (qVFamTensorBlock T b))

theorem rootThetaRegion_zeroLabel_eq_RmulO :
    rootThetaRegion (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
      (rootHalfCoefficient (l := l) T b) (zeroLabel l) = RmulO (l := l) T b := by
  unfold rootThetaRegion RmulO
  have hcoef : (fun i : qVFamTensorV =>
      (gaussExponent (zeroLabel l).1).toNat * rootHalfCoefficient (l := l) T b i) =
      (fun _ => (0 : Real)) := by
    funext i
    simp [zeroLabel, LeanFormal.IUT.SourceLabelWeightedDiagonal.zeroLabel]
  rw [hcoef, arithmeticTupleFractionalLattice_zero]

theorem RmulO_subset_paperPossibleImages :
    RmulO (l := l) T b ⊆ paperPossibleImages (l := l) T b := by
  intro x hx
  rw [← rootThetaRegion_zeroLabel_eq_RmulO (l := l) T b] at hx
  exact Set.mem_iUnion.mpr ⟨zeroLabel l, hx⟩

theorem RmulO_subset_leastLambdaOHull :
    RmulO (l := l) T b ⊆
      leastLambdaOHull (l := l) T b (paperPossibleImages (l := l) T b) := by
  intro x hx
  simp only [leastLambdaOHull, Set.mem_iInter]
  intro H hH
  rcases hH with ⟨⟨c, rfl⟩, hPH⟩
  exact hPH (RmulO_subset_paperPossibleImages (l := l) T b hx)

theorem lambdaORegion_zero_eq_RmulO :
    lambdaORegion (l := l) T b (fun _ => (0 : Real)) = RmulO (l := l) T b := by
  unfold lambdaORegion qPilotClassicalRegion RmulO
  rw [arithmeticTupleFractionalLattice_zero]

theorem leastLambdaOHull_eq_RmulO :
    leastLambdaOHull (l := l) T b (paperPossibleImages (l := l) T b) =
      RmulO (l := l) T b := by
  apply le_antisymm
  · have h := leastLambdaOHull_subset_lambdaORegion_zero (l := l) T b
    rwa [lambdaORegion_zero_eq_RmulO (l := l) T b] at h
  · exact RmulO_subset_leastLambdaOHull (l := l) T b

theorem leastLambdaOHull_eq_holomorphic :
    leastLambdaOHull (l := l) T b (paperPossibleImages (l := l) T b) =
      (arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b)
        qVFamTensorTuple : Set (qVFamTensorBlock T b)) := by
  rw [leastLambdaOHull_eq_RmulO (l := l) T b]
  unfold RmulO
  have hmul : arithmeticTupleValuationIntegerLattice (qVFamTensorPlaces T b)
      qVFamTensorTuple * arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b)
        qVFamTensorTuple = arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :=
    arithmeticTupleValuationIntegerLattice_mul_holomorphicLattice
      (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
  rw [hmul]

theorem paperHullLog_eq_zero :
    paperHullLog (l := l) T b mu = 0 := by
  unfold paperHullLog
  rw [leastLambdaOHull_eq_RmulO (l := l) T b]
  unfold RmulO
  have hmul : arithmeticTupleValuationIntegerLattice (qVFamTensorPlaces T b)
      qVFamTensorTuple * arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b)
        qVFamTensorTuple = arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :=
    arithmeticTupleValuationIntegerLattice_mul_holomorphicLattice
      (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
  rw [hmul]
  rw [coefficient_arithmeticTupleHolomorphicLattice]
  exact arithmeticTupleNormalizedLogVolume_canonicalUnitReference
    (qVFamTensorPlaces T b) qVFamTensorTuple mu

theorem paperHullLog_independent_of_q_order :
    paperHullLog (l := l) T b mu = 0 := paperHullLog_eq_zero (l := l) T b mu

def rows : List (String × String × String) :=
  [ ("rootThetaRegion_zeroLabel_eq_RmulO", "j=0 term = R*O", "PROVED"),
    ("RmulO_subset_leastLambdaOHull", "least hull ⊇ R*O", "PROVED"),
    ("leastLambdaOHull_eq_RmulO", "least hull = R*O", "PROVED"),
    ("paperHullLog_eq_zero", "q-order independent; old S800 hull", "PROVED; cf. S779:204-212, S793:170-171"),
    ("paper-faithful NonzeroHull", "different object", "GAP: not identified") ]

theorem rows_length : rows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1PaperHullZeroLabelActual

end