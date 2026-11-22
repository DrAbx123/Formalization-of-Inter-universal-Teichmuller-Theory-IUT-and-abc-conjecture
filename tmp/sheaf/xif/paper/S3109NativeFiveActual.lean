import tmp.sheaf.xif.paper.C3DonorFieldsFromSource
import tmp.sheaf.n8.closure.NativeC3
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceLogKummerIdentification
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.XiFPaper.C3DonorFieldsFromSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3109NativeFiveActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Exact p=5 target for a native input. -/
def S3109NativeC3PrimeFiveTarget : Prop :=
  nativeC3Prime X = 5

/-- The concrete Gaussian five place has rational prime 5 (actual bridge). -/
theorem S3109_concreteGaussianFivePlace_rationalPrime :
    (completionRationalPrime concreteGaussianFivePlace).val = 5 := by
  simpa [ConcreteSourceFrobenioidBridge.concretePlace] using
    concretePlace_rationalPrime_eq_five

/-- nativeC3Prime is by definition the rational prime of the native bad base
place; p=5 is exactly the corresponding rational-prime equality. -/
theorem S3109_nativeC3Prime_eq_five_of_prime_eq
    (h : (completionRationalPrime (nativeBadBasePlace X)).val = 5) :
    S3109NativeC3PrimeFiveTarget X :=
  h

/-- Unconditional but degenerate NativeTensorLandingDonor: empty tensor index,
p = 2, constant-one landing.  This is not the actual source tensor donor. -/
noncomputable def S3109ConstantOneDonor : NativeTensorLandingDonor.{0, 0} X where
  p := 2
  hp := inferInstance
  tensorIndex := Empty
  tensorFintype := inferInstance
  tensorPlaceIndex := fun _ => Empty
  tensorPlaces := fun i => i.elim
  tensorTuple := fun i => i.elim
  tensorUnit := 1
  tensorLanding := fun _ => 1
  tensorLanding_q := fun _ => rfl

theorem S3109_nativeTensorLandingDonor_nonempty :
    Nonempty (NativeTensorLandingDonor.{0, 0} X) :=
  ⟨S3109ConstantOneDonor X⟩

/-- But this donor has p = 2, not p = 5. -/
theorem S3109_constantOneDonor_p :
    (S3109ConstantOneDonor X).p = 2 := rfl

#check S3109NativeC3PrimeFiveTarget
#check S3109_concreteGaussianFivePlace_rationalPrime
#check S3109_nativeC3Prime_eq_five_of_prime_eq
#check S3109ConstantOneDonor
#check S3109_nativeTensorLandingDonor_nonempty
#check S3109_constantOneDonor_p
#print axioms S3109_concreteGaussianFivePlace_rationalPrime
#print axioms S3109_nativeC3Prime_eq_five_of_prime_eq
#print axioms S3109_nativeTensorLandingDonor_nonempty

end LeanFormal.IUT.XiFPaper.S3109NativeFiveActual
end