import tmp.sheaf.xif.paper.C3LogShellTensorHolomorphicHullActual

/-! # Compiling replacement for the C3 lambda-O normalized scalar

The old scalar is ENNReal.toReal, which conflates 0 and top to 0.  The
replacement below uses actual finite positive Haar data on both the unit region
and the lambda-scaled region, and forms the finite positive ratio

  scalingRatio = (mu (lambda * O)).toReal / (mu O).toReal.

The normalized log scalar is log of that ratio.  Under the actual normalization
data and lambda != 1 it is nonzero; no zero/top value is mapped to zero.

No sorry, axiom, True, or PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.C3LambdaONormalizedScalarActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open MeasureTheory

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (lam : HullBlock C3)

/-- The actual unit region of the C3 log-shell tensor packet. -/
abbrev c3UnitRegion : Set (HullBlock C3) := actualUnitRegion C3

/-- The actual lambda-scaled region lambda * O. -/
abbrev c3ScaledRegion : Set (HullBlock C3) := actualScaledRegion C3 lam

/-- Actual Haar of the unit region. -/
noncomputable def c3UnitHaar : ENNReal :=
  actualC3LogShellTensorHaar C3 (c3UnitRegion C3)

/-- Actual Haar of the lambda-scaled region. -/
noncomputable def c3ScaledHaar : ENNReal :=
  actualC3LogShellTensorHaar C3 (c3ScaledRegion C3 lam)

/-- The too-weak old scalar under audit. -/
noncomputable def oldC3LambdaOHullScalar : Real :=
  (c3ScaledHaar C3 lam).toReal

theorem oldC3LambdaOHullScalar_zero_of_zero
    (h : c3ScaledHaar C3 lam = 0) : oldC3LambdaOHullScalar C3 lam = 0 := by
  unfold oldC3LambdaOHullScalar
  rw [h]
  simp

theorem oldC3LambdaOHullScalar_zero_of_top
    (h : c3ScaledHaar C3 lam = ⊤) : oldC3LambdaOHullScalar C3 lam = 0 := by
  unfold oldC3LambdaOHullScalar
  rw [h]
  simp

/-- Actual normalization data: both Haar measures are finite and positive, so
the ratio is a genuine positive finite real. -/
structure C3LambdaONormalizationData where
  unit_measure_pos : 0 < c3UnitHaar C3
  unit_measure_lt_top : c3UnitHaar C3 < ⊤
  scaled_measure_pos : 0 < c3ScaledHaar C3 lam
  scaled_measure_lt_top : c3ScaledHaar C3 lam < ⊤
  scalingRatio : Real
  scalingRatio_eq : scalingRatio =
    (c3ScaledHaar C3 lam).toReal / (c3UnitHaar C3).toReal
  scalingRatio_ne_one_of_ne : lam ≠ (1 : HullBlock C3) → scalingRatio ≠ 1

/-- The actual normalized ratio is positive, proved from finite positive Haar
of both regions; no top/zero toReal conflation. -/
theorem C3LambdaONormalizationData.scalingRatio_pos
    (N : C3LambdaONormalizationData C3 lam) : 0 < N.scalingRatio := by
  rw [N.scalingRatio_eq]
  exact div_pos
    (ENNReal.toReal_pos N.scaled_measure_pos.ne' N.scaled_measure_lt_top.ne)
    (ENNReal.toReal_pos N.unit_measure_pos.ne' N.unit_measure_lt_top.ne)

/-- Actual normalized lambda-O hull log scalar. -/
noncomputable def c3LambdaONormalizedLogScalar
    (N : C3LambdaONormalizationData C3 lam) : Real :=
  Real.log N.scalingRatio

theorem c3LambdaONormalizedLogScalar_eq
    (N : C3LambdaONormalizationData C3 lam) :
    c3LambdaONormalizedLogScalar C3 lam N =
      Real.log ((c3ScaledHaar C3 lam).toReal / (c3UnitHaar C3).toReal) := by
  unfold c3LambdaONormalizedLogScalar
  rw [N.scalingRatio_eq]

/-- Under the actual normalization data and lambda != 1, the normalized log
scalar is nonzero. -/
theorem c3LambdaONormalizedLogScalar_ne_zero
    (N : C3LambdaONormalizationData C3 lam)
    (hlam : lam ≠ (1 : HullBlock C3)) :
    c3LambdaONormalizedLogScalar C3 lam N ≠ 0 := by
  unfold c3LambdaONormalizedLogScalar
  intro h
  have hpos := N.scalingRatio_pos
  rcases (Real.log_eq_zero.mp h) with h0 | h1 | hm1
  · linarith
  · exact N.scalingRatio_ne_one_of_ne hlam h1
  · linarith

end LeanFormal.IUT.XiFPaper.C3LambdaONormalizedScalarActual

end
