import tmp.sheaf.xif.paper.S914PaperLVExInstantiationActual
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual

/-! # S921: positivity of the paper qPilot region R

R = qPilotPaperRegion = thetaTensorScaledRegion at paperRootCoefficientFamily.
The region is a fractional-lattice times holomorphic-lattice submodule, so
0 ∈ R.  Positivity of its Haar measure is reduced to the exact minimal
condition that R has nonempty interior (equivalently contains a ball); then
Haar open-positivity gives 0 < mu R.  No equality/scaling data is used.
-/

noncomputable section
open scoped BigOperators Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S921RQpilotPaperRegionPositivityActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S914PaperLVExInstantiationActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]

/-- `0` lies in the paper qPilot region: it is a submodule region. -/
theorem s921R_zero_mem : (0 : qVFamTensorBlock T b) ∈ s914R (l := l) T b := by
  unfold s914R qPilotPaperRegion thetaTensorScaledRegion
  change (0 : qVFamTensorBlock T b) ∈
    (((arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
      qVFamTensorTuple (paperRootCoefficientFamily (l := l) T b)) *
      (arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b)
        qVFamTensorTuple) : Submodule ℤ_[(qVFamTensorP T b)]
          (qVFamTensorBlock T b)) : Set (qVFamTensorBlock T b))
  simpa using
    (Submodule.mul_mem_mul
      (Submodule.zero_mem (arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
        qVFamTensorTuple (paperRootCoefficientFamily (l := l) T b)))
      (Submodule.zero_mem (arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b)
        qVFamTensorTuple)))

theorem s921R_nonempty : (s914R (l := l) T b).Nonempty :=
  ⟨0, s921R_zero_mem (l := l) T b⟩

/-- Exact minimal positivity condition: R has nonempty interior, i.e. contains
a nonempty open ball. -/
def S921RInteriorNonempty : Prop :=
  (interior (s914R (l := l) T b)).Nonempty

theorem s921R_measure_pos_of_interior
    (h : S921RInteriorNonempty (l := l) T b) :
    0 < mu (s914R (l := l) T b) := by
  have hne : mu (interior (s914R (l := l) T b)) ≠ 0 :=
    Measure.IsOpenPosMeasure.open_pos (interior (s914R (l := l) T b))
      isOpen_interior h
  exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hne) (measure_mono interior_subset)

/-- Exact positivity goal, recorded without equality data. -/
def S921RMeasurePositive : Prop :=
  0 < mu (s914R (l := l) T b)

theorem s921RMeasurePositive_of_interior
    (h : S921RInteriorNonempty (l := l) T b) :
    S921RMeasurePositive (l := l) T b mu :=
  s921R_measure_pos_of_interior (l := l) T b mu h

end LeanFormal.IUT.XiFPaper.S921RQpilotPaperRegionPositivityActual

end
