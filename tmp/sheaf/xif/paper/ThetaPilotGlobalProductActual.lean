import tmp.sheaf.xif.paper.ThetaPilotGlobalObjectActual

/-! # Actual global product of Theta-pilot factor objects

ThetaPilotGlobalObjectActual constructs, for each F_l^x label j, the actual
model-Frobenioid factor object

  thetaPilotGlobalFactor j
    : SourceModelFrobenioid.Object (presentationDivisorMonoid X)

with divisor class Grothendieck.of (thetaVZeroLocusEffectiveGlobal j).

The paper Theta-pilot object is the product over j in F_l^x.  The current
SourceModelFrobenioid architecture does not expose a product category of
objects; what it does expose is the actual global divisor monoid.  In the
divisor monoid the product of factor objects corresponds to the finite sum of
their effective divisors.  This file therefore constructs the actual finite
divisor sum

  thetaPilotTotalDivisor = sum_{j in F_l^x} thetaVZeroLocusEffectiveGlobal j

and the model-Frobenioid object with that total divisor class.  This is the
actual divisor-monoid/object-class realization of the product over labels, not
a value-layer function space and not a fake product category.

The missing categorical product object (in a product Frobenioid category) is
recorded separately in the module documentation; no such category is claimed.
No inequality/fake object/sorry. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.ThetaPilotGlobalProductActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceModelBackend
open LeanFormal.IUT.XiFPaper.GlobalFrobenioidPresentationActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalObjectActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.ThetaPilotGlobalObjectActual

universe u

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)
variable [Fintype (Bad (nativePlaceSelection X.S))]

/-- The actual total Theta-pilot divisor: the finite sum over all F_l^x labels
of the actual global theta factor divisors. -/
noncomputable def thetaPilotTotalDivisor : EffectiveDivisor (BaseField X) :=
  ∑ j : ProcessionLabel l, thetaVZeroLocusEffectiveGlobal X j

/-- The total divisor is the finite sum of the actual factor divisors. -/
theorem thetaPilotTotalDivisor_eq_sum :
    thetaPilotTotalDivisor X =
      ∑ j : ProcessionLabel l, thetaVZeroLocusEffectiveGlobal X j := rfl

/-- The actual global Theta-pilot product object in the model Frobenioid:
bottom base and divisor class of the total finite sum. -/
noncomputable def thetaPilotGlobalProductObject :
    Iut.SourceModelFrobenioid.Object (presentationDivisorMonoid (X := X)) where
  base := bottomPoint
  divisorClass := Algebra.GrothendieckAddGroup.of (thetaPilotTotalDivisor X)

/-- The product object's base is the unique bottom object. -/
theorem thetaPilotGlobalProductObject_base :
    (thetaPilotGlobalProductObject X).base = bottomPoint := rfl

/-- The product object's divisor class is the actual total divisor class. -/
theorem thetaPilotGlobalProductObject_divisorClass :
    (thetaPilotGlobalProductObject X).divisorClass =
      Algebra.GrothendieckAddGroup.of (thetaPilotTotalDivisor X) := rfl

/-- The product object's divisor class is the class of the finite sum of the
factor divisors. -/
theorem thetaPilotGlobalProductObject_divisorClass_eq_sum :
    (thetaPilotGlobalProductObject X).divisorClass =
      Algebra.GrothendieckAddGroup.of
        (∑ j : ProcessionLabel l, thetaVZeroLocusEffectiveGlobal X j) := rfl

/-- Actual global Theta-pilot product data: factor objects, total divisor, and
the model object carrying the total divisor class. -/
structure ThetaPilotGlobalProductData where
  factor : ProcessionLabel l →
    Iut.SourceModelFrobenioid.Object (presentationDivisorMonoid (X := X))
  factor_eq : factor = thetaPilotGlobalFactor X
  totalDivisor : EffectiveDivisor (BaseField X)
  totalDivisor_eq : totalDivisor = thetaPilotTotalDivisor X
  productObject : Iut.SourceModelFrobenioid.Object
    (presentationDivisorMonoid (X := X))
  productObject_eq : productObject = thetaPilotGlobalProductObject X

/-- The actual product data from the factor family and the total divisor/object. -/
noncomputable def thetaPilotGlobalProductData :
    ThetaPilotGlobalProductData X where
  factor := thetaPilotGlobalFactor X
  factor_eq := rfl
  totalDivisor := thetaPilotTotalDivisor X
  totalDivisor_eq := rfl
  productObject := thetaPilotGlobalProductObject X
  productObject_eq := rfl

/-- Projection: each factor's divisor class is the actual theta divisor class. -/
theorem thetaPilotGlobalProductData_factor_divisorClass
    (j : ProcessionLabel l) :
    ((thetaPilotGlobalProductData X).factor j).divisorClass =
      Algebra.GrothendieckAddGroup.of (thetaVZeroLocusEffectiveGlobal X j) := rfl

/-- Projection: the product object's divisor class is the total divisor class. -/
theorem thetaPilotGlobalProductData_product_divisorClass :
    (thetaPilotGlobalProductData X).productObject.divisorClass =
      Algebra.GrothendieckAddGroup.of (thetaPilotTotalDivisor X) := rfl

end LeanFormal.IUT.XiFPaper.ThetaPilotGlobalProductActual

end
