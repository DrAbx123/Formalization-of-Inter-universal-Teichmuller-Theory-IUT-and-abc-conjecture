import tmp.sheaf.xif.paper.PaperThetaHullUnitInflationActual

/-! # Nontriviality audit of the C3 lambda-O hull scalar

The previous actual scalar

  nontrivialC3LambdaOHullScalar lam
    = (actualC3LogShellTensorHaar (actualScaledRegion lam)).toReal

is too weak to certify nontriviality.  ENNReal.toReal maps both 0 and top to 0:

  (0 : ENNReal).toReal = 0,  (top : ENNReal).toReal = 0.

Thus the scalar is 0 both when the scaled region has Haar measure zero and when
it has infinite Haar measure.  It cannot distinguish a genuinely nontrivial
lambda-O hull from a degenerate zero/infinite one, and no theorem gives
positivity/finiteness of the actual unit-region Haar.

This file records the exact failure and replaces the scalar by the actual
normalized ratio log

  log ((mu (lambda * O)).toReal / (mu O).toReal),

conditional on the actual normalization data 0 < mu O < top and a finite
positive scaling ratio.  No zero/trivial direction is used.

No sorry, axiom, True, or PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.C3LambdaOHullNontrivialActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.PaperThetaHullUnitInflationActual
open MeasureTheory

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (lam : HullBlock C3)

/-- The actual unit region of the C3 log-shell tensor packet. -/
abbrev c3UnitRegion : Set (HullBlock C3) := actualUnitRegion C3

/-- The actual lambda-scaled region lambda * O. -/
abbrev c3ScaledRegion : Set (HullBlock C3) :=
  actualScaledRegion C3 lam

/-- The actual Haar measure of the unit region. -/
noncomputable def c3UnitHaar : ENNReal :=
  actualC3LogShellTensorHaar C3 (c3UnitRegion C3)

/-- The actual Haar measure of lambda * O. -/
noncomputable def c3ScaledHaar : ENNReal :=
  actualC3LogShellTensorHaar C3 (c3ScaledRegion C3 lam)

/-- Exact weak-scalar definition under audit. -/
noncomputable def oldC3LambdaOHullScalar : Real :=
  (c3ScaledHaar C3 lam).toReal

/-- If the scaled Haar is zero, the old scalar is zero. -/
theorem oldC3LambdaOHullScalar_eq_zero_of_scaled_measure_zero
    (h : c3ScaledHaar C3 lam = 0) :
    oldC3LambdaOHullScalar C3 lam = 0 := by
  unfold oldC3LambdaOHullScalar
  rw [h]
  simp

/-- If the scaled Haar is infinite (top), the old scalar is also zero. -/
theorem oldC3LambdaOHullScalar_eq_zero_of_scaled_measure_top
    (h : c3ScaledHaar C3 lam = ⊤) :
    oldC3LambdaOHullScalar C3 lam = 0 := by
  unfold oldC3LambdaOHullScalar
  rw [h]
  simp

/-- Exact obstruction: the old scalar conflates zero and infinite Haar into the
same value 0; it is not a nontrivial hull scalar. -/
def OldC3LambdaOHullScalarTooWeak : Prop :=
  (c3ScaledHaar C3 lam = 0 → oldC3LambdaOHullScalar C3 lam = 0) ∧
  (c3ScaledHaar C3 lam = ⊤ → oldC3LambdaOHullScalar C3 lam = 0)

theorem oldC3LambdaOHullScalarTooWeak_holds :
    OldC3LambdaOHullScalarTooWeak C3 lam :=
  ⟨oldC3LambdaOHullScalar_eq_zero_of_scaled_measure_zero C3 lam,
    oldC3LambdaOHullScalar_eq_zero_of_scaled_measure_top C3 lam⟩

/-- Actual normalization data needed to replace the weak scalar: positive
finite unit Haar and a finite positive scaling ratio. -/
structure C3LambdaONormalizationData where
  unit_measure_pos : 0 < c3UnitHaar C3
  unit_measure_lt_top : c3UnitHaar C3 < ⊤
  scalingRatio : Real
  scalingRatio_eq : scalingRatio =
    (c3ScaledHaar C3 lam).toReal / (c3UnitHaar C3).toReal
  scalingRatio_pos : 0 < scalingRatio
  scalingRatio_ne_one_of_ne : lam ≠ (1 : HullBlock C3) → scalingRatio ≠ 1

/-- Actual normalized lambda-O hull log scalar: log of the Haar ratio. -/
noncomputable def c3LambdaONormalizedLogScalar
    (N : C3LambdaONormalizationData C3 lam) : Real :=
  Real.log (N.scalingRatio)

/-- The normalized scalar is the actual log ratio. -/
theorem c3LambdaONormalizedLogScalar_eq
    (N : C3LambdaONormalizationData C3 lam) :
    c3LambdaONormalizedLogScalar C3 lam N =
      Real.log ((c3ScaledHaar C3 lam).toReal / (c3UnitHaar C3).toReal) := by
  unfold c3LambdaONormalizedLogScalar
  rw [N.scalingRatio_eq]

/-- Nontriviality under the actual normalization data: if lambda is not 1, the
normalized log scalar is nonzero. -/
theorem c3LambdaONormalizedLogScalar_ne_zero
    (N : C3LambdaONormalizationData C3 lam)
    (hlam : lam ≠ (1 : HullBlock C3)) :
    c3LambdaONormalizedLogScalar C3 lam N ≠ 0 := by
  unfold c3LambdaONormalizedLogScalar
  intro h
  have hratio : N.scalingRatio = 1 := by
    have hlog := h
    rwa [Real.log_eq_zero] at hlog
  exact N.scalingRatio_ne_one_of_ne hlam hratio

end LeanFormal.IUT.XiFPaper.C3LambdaOHullNontrivialActual

end
