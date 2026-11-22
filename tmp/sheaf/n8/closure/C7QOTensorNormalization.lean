import tmp.sheaf.n8.closure.C7PaperDivisorActual2

/-!
# C7 qO/tensor normalization: Q vs R

Actual quantities:
  Q = qORegionLogVolume X < 0  (qO)
  h = paper C6 Theta = c6Theta.toReal
  R = paper C6 region volume = c6RegionVolume.toReal,  R <= h.

Two natural divisor normalizations:

1. A = R, Z = h - R (hull-excess zero): law h - Q = Z - A iff Q = 2R.
   This double-counts: Q = 2R is not the same-region identification.

2. A = R, Z = h (Theta as effective zero): law h - Q = Z - A iff Q = R.
   This is the correct same-region normalization; production gives no Q=R.

No arbitrary A/Z; both choices are actual region/hull volumes.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaVaryingCalibrationQOActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.PaperC6RegionConstructed2
open LeanFormal.IUT.N8Closure.C7PaperDivisorActual2

namespace LeanFormal.IUT.N8Closure.C7QOTensorNormalization

variable {l : PrimeGeFive} (X : N8NativeInput l) (S : SourceInitialThetaData l)
  (P : PaperC6RegionInput S)

/-- Actual qO endpoint negative. -/
theorem Q_neg : Q X < 0 := by
  rw [Q, qORegionLogVolume_eq_qPilotSignedLog X]
  exact qPilotSignedLog_neg X

/-- Alternative effective zero: the full Theta/hull log-volume. -/
noncomputable def ZTheta : Real := hTheta S P

/-- Correct same-region law with A=R (region volume), Z=Theta (hull volume). -/
def C7LawThetaZero : Prop := hTheta S P - Q X = ZTheta S P - A S P

/-- The correct law is equivalent to Q = R, not Q = 2R. -/
theorem c7LawThetaZero_iff_Q_eq_region :
    C7LawThetaZero X S P ↔ Q X = rRegion S P := by
  unfold C7LawThetaZero ZTheta A
  constructor <;> intro hh <;> linarith

/-- The old hull-excess law is equivalent to Q = 2R. -/
theorem c7LawHullExcess_iff_Q_eq_two_region :
    C7Law X S P ↔ Q X = 2 * rRegion S P :=
  c7Law_iff_Q_eq_two_region X S P

/-- Correct normalization: Q = R (same region log-volume). -/
def CorrectNormalization : Prop := Q X = rRegion S P

/-- Incorrect double-counting normalization: Q = 2R. -/
def DoubleCountingNormalization : Prop := Q X = 2 * rRegion S P

/-- If the region volume is nonnegative, Q<0 rules out Q=2R. -/
theorem doubleCounting_false_of_region_nonneg (hR : 0 <= rRegion S P) :
    Q X ≠ 2 * rRegion S P := by
  intro h
  have hQ := Q_neg X
  nlinarith

/-- Exact missing source identification: qO region volume = paper C6 region
volume.  This is the correct Q=R normalization. -/
def MissingQORegionIdentification : Prop := CorrectNormalization X S P

end LeanFormal.IUT.N8Closure.C7QOTensorNormalization
