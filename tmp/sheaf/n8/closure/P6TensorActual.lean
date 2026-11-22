import tmp.sheaf.n8.closure.C3KummerActual
import tmp.sheaf.n8.closure.P6Tensor
import tmp.sheaf.n8.closure.NativeC3
import Mathlib

/-!
# P6 tensor actual: native actual q/roots with the tensor landing obligation

This file reuses NativeC3.nativeQDonorActual and the actual roots/Kummer class,
and packages them with a P6 tensor landing donor.

The only missing piece remains NativeTensorLandingDonor.  Its tensorLanding_q
field quantifies over all NativeQDonor D, while the native actual q is one fixed
source witness; no uniform actual completion-to-tensor map is available.  The
file records this exact obstruction and does not construct an arbitrary map.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.P6TensorActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C3KummerActual
open LeanFormal.IUT.N8Closure.P6Tensor
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v w

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual native q donor from Clause (b). -/
abbrev actualQDonor : NativeQDonor X := nativeQDonorActual X

/-- The actual native q candidate, q-unit, roots and Kummer class reused from
NativeC3/C3KummerActual. -/
abbrev actualQ : NumberFieldFinitePlace.FinitePlaceQCandidate (nativeFPlaceOverBad X) :=
  nativeQActual X

abbrev actualQUnit : (NumberFieldFinitePlace.Completion (nativeFPlaceOverBad X))ˣ :=
  nativeQUnitActual X

abbrev actualRoots : NatRootSystem (nativeQUnitAlgClosedActual X) :=
  nativeRoots X (nativeQDonorActual X)

abbrev actualKummerClass :
    CyclotomicTower (AlgebraicClosure (NumberFieldFinitePlace.Completion
      (nativeFPlaceOverBad X))) :=
  nativeKummerClass X (nativeQDonorActual X)

/-- P6 actual tensor package: actual native q/roots/Kummer data plus the P6
tensor landing interface. -/
structure P6ActualTensorPackage (L : P6TensorLandingData X) where
  q : NumberFieldFinitePlace.FinitePlaceQCandidate (nativeFPlaceOverBad X) := actualQ X
  qUnit : (NumberFieldFinitePlace.Completion (nativeFPlaceOverBad X))ˣ := actualQUnit X
  roots : NatRootSystem (nativeQUnitAlgClosedActual X) := actualRoots X
  kummerClass : CyclotomicTower (AlgebraicClosure
    (NumberFieldFinitePlace.Completion (nativeFPlaceOverBad X))) := actualKummerClass X
  p6 : P6C3TensorOutput X (actualQDonor X) L
  qTensor : ArithmeticTensorTupleBlock L.tensorPlaces L.tensorTuple :=
    L.tensorLanding (actualQ X).q
  qTensor_eq : L.tensorLanding (actualQ X).q =
    (L.tensorUnit : ArithmeticTensorTupleBlock L.tensorPlaces L.tensorTuple) :=
    L.tensorLanding_q (actualQDonor X)

/-- Zero-sorry construction from an actual tensor landing donor. -/
noncomputable def p6ActualTensorPackageOfLanding (L : P6TensorLandingData X) :
    P6ActualTensorPackage X L where
  q := actualQ X
  qUnit := actualQUnit X
  roots := actualRoots X
  kummerClass := actualKummerClass X
  p6 := p6C3TensorOutputOfDonors X (actualQDonor X) L
  qTensor := L.tensorLanding (actualQ X).q
  qTensor_eq := L.tensorLanding_q (actualQDonor X)

/-- Reuse of the actual q landing once a tensor donor is supplied. -/
theorem p6ActualTensor_q_landing (L : P6TensorLandingData X) :
    L.tensorLanding (actualQ X).q =
      (L.tensorUnit : ArithmeticTensorTupleBlock L.tensorPlaces L.tensorTuple) :=
  L.tensorLanding_q (actualQDonor X)

end LeanFormal.IUT.N8Closure.P6TensorActual
