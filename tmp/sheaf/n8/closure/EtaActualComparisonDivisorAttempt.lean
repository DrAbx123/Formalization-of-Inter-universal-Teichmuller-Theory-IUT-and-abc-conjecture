import tmp.sheaf.n8.closure.EtaLocalGlobalObstructionActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleHullVolume

/-!
# Eta actual comparison divisor attempt

Actual endpoint computations:

* qO: Q = qORegionLogVolume X = qPilotSignedLog X < 0.
* tensor hull: h = arithmeticTupleHullUnitLogVolume places tuple, with h >= 0.

Thus the endpoint inequality h >= Q holds numerically.  However the two
quantities live in different carriers (native qO completion vs arithmetic
tensor block), and production supplies no actual local multiplier divisor A or
effective zero divisor Z, hence no model law d*alpha + Z = beta + A and no
kappa, S computation.  That is the exact missing target data; no arbitrary
divisor or h is introduced.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false

open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaVaryingCalibrationQOActual
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaLocalGlobalObstructionActual
open LeanFormal.IUT.NumberFieldFinitePlace

namespace LeanFormal.IUT.N8Closure.EtaActualComparisonDivisorAttempt

universe u v w

/-- Actual qO endpoint Q is negative. -/
theorem qO_Q_neg {l : PrimeGeFive} (X : N8NativeInput l) :
    qORegionLogVolume X < 0 := by
  rw [qORegionLogVolume_eq_qPilotSignedLog X]
  exact qPilotSignedLog_neg X

/-- Actual tensor hull endpoint h is nonnegative. -/
theorem hull_h_nonneg {K : Type u} [Field K] [NumberField K]
    {p : Nat} [Fact p.Prime] {ι : Type v} [Finite ι] {V : ι → Type w}
    (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i) :
    0 ≤ arithmeticTupleHullUnitLogVolume places tuple :=
  arithmeticTupleHullUnitLogVolume_nonneg places tuple

/-- Numeric endpoint inequality: any nonnegative tensor-hull h is >= the
negative qO Q. -/
theorem hull_ge_qO {l : PrimeGeFive} (X : N8NativeInput l)
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type v} [Finite ι] {V : ι → Type w}
    (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i) :
    qORegionLogVolume X ≤ arithmeticTupleHullUnitLogVolume places tuple :=
  le_of_lt (lt_of_lt_of_le (qO_Q_neg X) (hull_h_nonneg places tuple))

/-- Exact missing actual comparison-divisor data: an actual common carrier,
opposite tensor target h, local multiplier divisor A and effective zero Z with
the model law. -/
structure ActualComparisonDivisorData {l : PrimeGeFive} (X : N8NativeInput l) where
  Q : ℝ
  h : ℝ
  kappa : ℝ
  S : ℝ
  d : ℕ
  Q_actual : Q = qORegionLogVolume X
  identity : h - (d : ℝ) * Q = S - kappa
  S_nonneg : 0 ≤ S

end LeanFormal.IUT.N8Closure.EtaActualComparisonDivisorAttempt
