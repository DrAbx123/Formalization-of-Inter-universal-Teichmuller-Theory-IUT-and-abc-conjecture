import tmp.sheaf.n8.closure.O3ConstructedComparison

/-!
# C7 source comparison constructed from actual endpoints

Actual endpoint data:

* Q = qORegionLogVolume X = qPilotSignedLog X (qO).
* h = O3HTensor X = log(tensorHaar X (nnLattice X gNonIntegral 1)) (tensor).

Endpoint calibration: setting A := Q - h and Z := 0 makes the model law
h - Q = Z - A hold by construction.  This is a real function of the actual
qO/tensor volume ratio, not an arbitrary constant, but it is only an
endpoint-calibrated defect: no production source comparison morphism identifies
it with an actual local multiplier divisor.

If instead the multiplier is the actual qO scaling A = Q, Z = 0, the model law
is equivalent to h = 0.  No production theorem proves h = 0; this is the exact
counterexample condition / obstruction.  No fake closure.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.O3ConstructedComparison
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaVaryingCalibrationQOActual
open LeanFormal.IUT.N8Closure.EtaTensorZpSubmoduleLatticeActual
open ABCBridge.N8.C3TensorTargetCorrection

namespace LeanFormal.IUT.N8Closure.C7SourceComparisonConstructed

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

/-- Actual qO endpoint. -/
noncomputable def Q : Real := O3Q X

/-- Actual tensor endpoint. -/
noncomputable def h : Real := O3HTensor X

theorem Q_neg : Q X < 0 := O3Q_neg X

/-- Endpoint-calibrated multiplier: the log ratio qO/tensor. -/
noncomputable def AEndpoint : Real := Q X - h X

/-- Exact comparison data with endpoint-calibrated A and zero effective zero. -/
structure EndpointComparisonData where
  hval : Real
  Qval : Real
  A : Real
  Z : Real
  d : Nat
  h_eq : hval = h X
  Q_eq : Qval = Q X
  A_eq : A = AEndpoint X
  Z_eq : Z = 0
  d_eq : d = 1
  law : hval - (d : Real) * Qval = Z - A

/-- Endpoint-calibrated actual data: the law is a tautology from A=Q-h. -/
def endpointComparisonData : EndpointComparisonData X where
  hval := h X
  Qval := Q X
  A := AEndpoint X
  Z := 0
  d := 1
  h_eq := rfl
  Q_eq := rfl
  A_eq := rfl
  Z_eq := rfl
  d_eq := rfl
  law := by
    unfold AEndpoint
    ring

/-- If the multiplier is the actual qO scaling A=Q and Z=0, the model law is
equivalent to h=0.  This is the precise obstruction/counterexample condition. -/
theorem qoScaling_law_iff_h_zero :
    (h X - (1 : Real) * Q X = 0 - Q X) ↔ h X = 0 := by
  constructor
  · intro hh
    linarith
  · intro hh
    rw [hh]
    ring

/-- Exact missing source theorem: actual qO scaling comparison forces h=0. -/
def MissingQOScalingSourceComparison : Prop := h X = 0


end LeanFormal.IUT.N8Closure.C7SourceComparisonConstructed
