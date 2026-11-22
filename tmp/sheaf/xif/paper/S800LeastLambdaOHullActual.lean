import tmp.sheaf.xif.paper.RootNormalizedContainmentActual
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual
import tmp.sheaf.xif.paper.ThetaTensorScaledImageActual
import tmp.sheaf.xif.paper.SignedLabelOneActual

/-! # S800: least lambda-O holomorphic hull, hull first

Paper order: take the least lambda-O region H(P) containing the possible
images P, THEN take log-volume(H(P)).  This file defines H(P) as the
intersection of all actual scaled qVFam regions containing P, and proves
the paper qPilot region at order/(2l) (the j=1 theta region) is contained
in H(P).  The log is only taken after the hull is defined.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S800LeastLambdaOHullActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]
variable (mu : Measure (qVFamTensorBlock T b))
variable [Measure.IsAddHaarMeasure mu]

/-- Actual lambda-O candidate region at coefficient c. -/
noncomputable def lambdaORegion (c : qVFamTensorV → Real) :
    Set (qVFamTensorBlock T b) :=
  qPilotClassicalRegion (qVFamTensorPlaces T b) qVFamTensorTuple c

/-- Candidate lambda-O regions containing the possible-image set P. -/
def candidateHulls (P : Set (qVFamTensorBlock T b)) :
    Set (Set (qVFamTensorBlock T b)) :=
  {H | (∃ c : qVFamTensorV → Real, H = lambdaORegion (l := l) T b c) ∧ P ⊆ H}

/-- The paper least lambda-O holomorphic hull: intersection of all candidates. -/
noncomputable def leastLambdaOHull (P : Set (qVFamTensorBlock T b)) :
    Set (qVFamTensorBlock T b) :=
  ⋂ H ∈ candidateHulls (l := l) T b P, H

theorem subset_leastLambdaOHull (P : Set (qVFamTensorBlock T b)) :
    P ⊆ leastLambdaOHull (l := l) T b P := by
  intro x hx
  simp only [leastLambdaOHull, Set.mem_iInter]
  intro H hH
  exact hH.2 hx

theorem leastLambdaOHull_subset_candidate
    (P : Set (qVFamTensorBlock T b)) (H : Set (qVFamTensorBlock T b))
    (hH : H ∈ candidateHulls (l := l) T b P) :
    leastLambdaOHull (l := l) T b P ⊆ H := by
  intro x hx
  simp only [leastLambdaOHull, Set.mem_iInter] at hx
  exact hx H hH

/-- Paper qPilot region: j=1 theta region at c_root = order/(2l)-coefficient. -/
noncomputable def qPilotPaperRegion : Set (qVFamTensorBlock T b) :=
  thetaTensorScaledRegion (qVFamTensorPlaces T b) qVFamTensorTuple
    (rootHalfCoefficient (l := l) T b)

theorem qPilotPaperRegion_eq_rootThetaRegion_one :
    qPilotPaperRegion (l := l) T b =
      rootThetaRegion (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
        (rootHalfCoefficient (l := l) T b) (oneLabel l) := by
  unfold qPilotPaperRegion rootThetaRegion
  congr 1
  funext i
  rw [gaussExponent_oneLabel]
  ring

/-- Possible images P: the actual root theta image union at c_root. -/
noncomputable def paperPossibleImages : Set (qVFamTensorBlock T b) :=
  rootThetaImageSet (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
    (rootHalfCoefficient (l := l) T b)

theorem qPilotPaperRegion_subset_possibleImages :
    qPilotPaperRegion (l := l) T b ⊆ paperPossibleImages (l := l) T b := by
  rw [qPilotPaperRegion_eq_rootThetaRegion_one]
  exact Set.subset_iUnion
    (fun j : SignedLabel l.value =>
      rootThetaRegion (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
        (rootHalfCoefficient (l := l) T b) j) (oneLabel l)

/-- Paper qPilot region is contained in the least lambda-O hull H(P). -/
theorem qPilotPaperRegion_subset_leastLambdaOHull :
    qPilotPaperRegion (l := l) T b ⊆
      leastLambdaOHull (l := l) T b (paperPossibleImages (l := l) T b) := by
  exact (qPilotPaperRegion_subset_possibleImages (l := l) T b).trans
    (subset_leastLambdaOHull (l := l) T b (paperPossibleImages (l := l) T b))

/-- Log is taken only AFTER the hull. -/
noncomputable def paperHullLog : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
    mu (leastLambdaOHull (l := l) T b (paperPossibleImages (l := l) T b))

/-- Exact log after hull: qPilot region log with the paper half coefficient. -/
noncomputable def qPilotPaperRegionLog : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
    mu (qPilotPaperRegion (l := l) T b)

/-- Conditional hull-first log comparison from positivity/finiteness. -/
theorem qPilotPaperRegionLog_le_paperHullLog
    (hpos : 0 < mu (qPilotPaperRegion (l := l) T b))
    (hfin : mu (leastLambdaOHull (l := l) T b
      (paperPossibleImages (l := l) T b)) < ⊤) :
    qPilotPaperRegionLog (l := l) T b mu ≤ paperHullLog (l := l) T b mu := by
  unfold qPilotPaperRegionLog paperHullLog
  apply arithmeticTupleNormalizedLogVolume_mono
  · exact qPilotPaperRegion_subset_leastLambdaOHull (l := l) T b
  · exact hpos
  · exact hfin

end LeanFormal.IUT.XiFPaper.S800LeastLambdaOHullActual
end
