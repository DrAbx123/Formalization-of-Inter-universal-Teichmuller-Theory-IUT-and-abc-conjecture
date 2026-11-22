import tmp.sheaf.n8.closure.NativeReductionRestActual

/-!
# Native qParameter actual attempt

Clause B gives a SourceTateComparisonWitness at every bad place's lifted
F-place.  Its parameter is a FinitePlaceQCandidate, whose q lives in the local
completion and whose discrete valuation exponent is actual and positive.

We build the real contract qParameter as the positive discrete log-norm

  qParameter b = exp (-(exponent of the Tate q at b)).

This is actual from the native witness, not an arbitrary Real.  It proves:
nonzero, norm < 1, q != 1, and the stable-reduction q != 1 compatibility.
The split-multiplicative card remains a separate Wave29 gap and is not used
here.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.NativeQParameterActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeContractFieldsActualAttempt
open LeanFormal.IUT.N8Closure.NativePartitionInputsActual
open LeanFormal.IUT.N8Closure.NativeBadFintypeSourceAttempt
open LeanFormal.IUT.N8Closure.NativeBadFiniteTargetCorrection
open LeanFormal.IUT.N8Closure.NativeContractFromBadFinite
open LeanFormal.IUT.N8Closure.NativeReductionRestActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source

variable {l : PrimeGeFive}

/-- Native Tate comparison witness at a bad place, from Clause B. -/
noncomputable def nativeTateWitness (X : N8NativeInput l)
    (b : NativeBadPlaces X) :
    SourceTateComparisonWitness X.S.arithmetic (nativeBadLift X b) :=
  Classical.choice (X.S.clauseB.q_comparison (nativeBadLift X b) (by
    rw [nativeBadLift_comap]
    exact b.2))

/-- Actual positive discrete valuation exponent of the Tate q. -/
def nativeQExponent (X : N8NativeInput l) (b : NativeBadPlaces X) : Int :=
  (nativeTateWitness X b).parameter.exponent

theorem nativeQExponent_pos (X : N8NativeInput l)
    (b : NativeBadPlaces X) : 0 < nativeQExponent X b :=
  (nativeTateWitness X b).parameter.exponent_pos

/-- Actual real qParameter: the positive discrete log-norm. -/
def nativeQParameter (X : N8NativeInput l) (b : NativeBadPlaces X) : Real :=
  Real.exp (-((nativeQExponent X b : Int) : Real))

theorem nativeQParameter_ne_zero (X : N8NativeInput l)
    (b : NativeBadPlaces X) : nativeQParameter X b ≠ 0 :=
  Real.exp_ne_zero _

theorem nativeQParameter_contracting (X : N8NativeInput l)
    (b : NativeBadPlaces X) : ‖nativeQParameter X b‖ < 1 := by
  have hpos : 0 < (nativeQExponent X b : Real) := by
    exact_mod_cast nativeQExponent_pos X b
  have hneg : -((nativeQExponent X b : Int) : Real) < 0 := by
    linarith
  rw [nativeQParameter]
  rw [Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))]
  exact Real.exp_lt_one_iff.mpr hneg

theorem nativeQParameter_ne_one (X : N8NativeInput l)
    (b : NativeBadPlaces X) : nativeQParameter X b ≠ 1 := by
  intro h
  have hExp : Real.exp (-((nativeQExponent X b : Int) : Real)) = Real.exp 0 := by
    simpa [nativeQParameter] using h
  have harg := Real.exp_injective hExp
  have hpos : 0 < (nativeQExponent X b : Real) := by
    exact_mod_cast nativeQExponent_pos X b
  linarith

/-- Actual q != 1 compatibility under stable reduction. -/
theorem nativeQParameter_reduction_compatibility
    (X : N8NativeInput l) (b : NativeBadPlaces X)
    (_hstable :
      X.S.arithmetic.curve.HasStableReductionAt (nativeBadLift X b)) :
    nativeQParameter X b ≠ 1 :=
  nativeQParameter_ne_one X b

/-- Actual q-parameter data package; no arbitrary Real. -/
structure NativeQParameterData (X : N8NativeInput l) where
  qParameter : NativeBadPlaces X → Real
  qParameter_nonzero : ∀ b, qParameter b ≠ 0
  qParameter_contracting : ∀ b, ‖qParameter b‖ < 1
  qParameter_ne_one : ∀ b, qParameter b ≠ 1

/-- Actual package from the native Tate witnesses. -/
noncomputable def nativeQParameterData (X : N8NativeInput l) :
    NativeQParameterData X where
  qParameter := nativeQParameter X
  qParameter_nonzero := nativeQParameter_ne_zero X
  qParameter_contracting := nativeQParameter_contracting X
  qParameter_ne_one := nativeQParameter_ne_one X

end LeanFormal.IUT.N8Closure.NativeQParameterActual
