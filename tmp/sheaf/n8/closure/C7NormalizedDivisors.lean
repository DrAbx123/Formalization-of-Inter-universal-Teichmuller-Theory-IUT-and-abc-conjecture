import tmp.sheaf.n8.closure.PaperC6RegionConstructed2
import tmp.sheaf.n8.closure.C6NormalizedTensorHaar
import tmp.sheaf.n8.closure.C7PaperDivisorActual2
import tmp.sheaf.n8.closure.EtaQRegionRepresentation
import tmp.sheaf.n8.closure.C9QPilotRegion

/-!
# C7 normalized paper divisors

Use the actual normalized C6 tensor Haar (unit-region mass one):
  hNorm = c6NormalizedTheta.toReal
  rNorm = c6NormalizedRegionVolume.toReal
and the natural normalized divisors A = rNorm, Z = hNorm.

Then hNorm - Q = Z - A is equivalent to Q = rNorm.  This removes the raw-Haar
Q=2R double counting; the remaining exact target is Q=rNorm.
No arbitrary A/Z.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.PaperC6RegionConstructed2
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar
open LeanFormal.IUT.N8Closure.C7PaperDivisorActual2
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaVaryingCalibrationQOActual
open LeanFormal.IUT.N8Closure.C9QPilotRegion

namespace LeanFormal.IUT.N8Closure.C7NormalizedDivisors

/-- Normalized paper hull log-volume hNorm. -/
noncomputable def hNorm {l : PrimeGeFive} (S : SourceInitialThetaData l) : Real :=
  (c6NormalizedTheta (places S) (tuple S)).toReal

/-- Normalized paper region log-volume rNorm. -/
noncomputable def rNorm {l : PrimeGeFive} (S : SourceInitialThetaData l) : Real :=
  (c6NormalizedRegionVolume (places S) (tuple S)).toReal

/-- Actual qO endpoint. -/
noncomputable def Q {l : PrimeGeFive} (X : N8NativeInput l) : Real :=
  qORegionLogVolume X

/-- Normalized multiplier divisor A = rNorm. -/
noncomputable def A {l : PrimeGeFive} (S : SourceInitialThetaData l) : Real :=
  rNorm S

/-- Normalized effective zero Z = hNorm. -/
noncomputable def Z {l : PrimeGeFive} (S : SourceInitialThetaData l) : Real :=
  hNorm S

/-- Normalized model law with d=1, A=rNorm, Z=hNorm. -/
def C7NormalizedLaw {l : PrimeGeFive} (X : N8NativeInput l)
    (S : SourceInitialThetaData l) : Prop :=
  hNorm S - Q X = Z S - A S

/-- The normalized law is exactly Q = rNorm. -/
theorem c7NormalizedLaw_iff_Q_eq_rNorm {l : PrimeGeFive} (X : N8NativeInput l)
    (S : SourceInitialThetaData l) :
    C7NormalizedLaw X S ↔ Q X = rNorm S := by
  unfold C7NormalizedLaw Z A
  constructor <;> intro hh <;> linarith

/-- Actual qO endpoint is negative. -/
theorem Q_neg {l : PrimeGeFive} (X : N8NativeInput l) : Q X < 0 := by
  rw [Q, qORegionLogVolume_eq_qPilotSignedLog X]
  exact qPilotSignedLog_neg X

/-- If the normalized region volume is nonnegative, Q=rNorm is impossible. -/
theorem Q_ne_rNorm_of_nonneg {l : PrimeGeFive} (X : N8NativeInput l)
    (S : SourceInitialThetaData l) (hR : 0 <= rNorm S) : Q X ≠ rNorm S := by
  intro hh
  have hQ := Q_neg X
  linarith

/-- Exact remaining identification target. -/
def MissingQONormalizedIdentification {l : PrimeGeFive} (X : N8NativeInput l)
    (S : SourceInitialThetaData l) : Prop := Q X = rNorm S

end LeanFormal.IUT.N8Closure.C7NormalizedDivisors
