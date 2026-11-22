import tmp.sheaf.xif.paper.QPilotGlobalLogVolumeFromQActual
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual
import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv

/-! # Actual global Theta-pilot object on the global realified Frobenioid

This file uses the actual global realified Frobenioid presentation of
GlobalFrobenioidPresentationActual / QPilotGlobalObjectActual, not a value-layer
function space.

For each F_l^x label j (units, not SignedLabel including 0), the actual theta
value at a bad place b is

  thetaValueFamily j b = (qVFamily X.S b).q ^ thetaLabelExponent j,

where thetaLabelExponent j is the actual Gaussian exponent j^2.  The
corresponding effective divisor has multiplicity

  thetaLabelExponent j * qVEffectiveMultiplicity X b

at the underlying base prime of b.  Summing over V_bad gives the actual global
Theta-pilot divisor at label j, and its model-Frobenioid object is the unique
bottom object with Grothendieck class of that divisor.

The paper Theta-pilot object is the product over j in F_l^x of these factor
objects; this file constructs the actual factor family and its product object
data.  The product category itself is not claimed as a single SourceModelFrobenioid
object; the exact factor family is the actual content.  No value-layer carrier,
no constant tuple, no inequality.  No fake/axiom/sorry. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.ThetaPilotGlobalObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceModelBackend
open LeanFormal.IUT.XiFPaper.GlobalFrobenioidPresentationActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalObjectActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual

universe u

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)

/-- The actual finite F-place over a bad base place as a prime-tagged place. -/
noncomputable def nativeBadFPlaceAtPrime
    (b : Bad (nativePlaceSelection X.S)) :
    FinitePlaceAtPrime X.S.arithmetic.F
      (completionRationalPrime ((nativeBadLift X.S).lift b)).val :=
  ⟨(nativeBadLift X.S).lift b, rfl⟩

/-- The actual Gaussian exponent j^2 of an F_l^x unit label. -/
noncomputable def thetaLabelExponent (j : ProcessionLabel l) : Nat :=
  (gaussExponent
    (SignedLabel.representative l (j : ZMod l.value)).1).toNat

/-- The actual theta value family q_v^(j^2) at a bad place. -/
noncomputable def thetaValueFamily
    (j : ProcessionLabel l) (b : Bad (nativePlaceSelection X.S)) :
    CommonPrimeCompletion (K := X.S.arithmetic.F) (nativeBadFPlaceAtPrime X b) :=
  (qVFamily X.S b).q ^ thetaLabelExponent (l := l) j

/-- The actual theta value is the q_v power with the Gaussian exponent. -/
theorem thetaValueFamily_eq
    (j : ProcessionLabel l) (b : Bad (nativePlaceSelection X.S)) :
    thetaValueFamily X j b =
      (qVFamily X.S b).q ^ thetaLabelExponent (l := l) j := rfl

/-- The effective divisor of the theta value at one label and bad place:
multiplicity j^2 times the actual q_v multiplicity. -/
noncomputable def thetaVZeroLocusEffectiveDivisor
    (j : ProcessionLabel l) (b : Bad (nativePlaceSelection X.S)) :
    EffectiveDivisor (BaseField X) :=
  (Finsupp.single (underlyingPrime b.1)
      (thetaLabelExponent (l := l) j * qVEffectiveMultiplicity X b), 0)

/-- The global effective divisor of the Theta-pilot factor at label j. -/
noncomputable def thetaVZeroLocusEffectiveGlobal
    [Fintype (Bad (nativePlaceSelection X.S))] (j : ProcessionLabel l) :
    EffectiveDivisor (BaseField X) :=
  ∑ b : Bad (nativePlaceSelection X.S),
    thetaVZeroLocusEffectiveDivisor X j b

/-- The actual model-Frobenioid Theta-pilot factor object at label j. -/
noncomputable def thetaPilotGlobalFactor
    [Fintype (Bad (nativePlaceSelection X.S))] (j : ProcessionLabel l) :
    Iut.SourceModelFrobenioid.Object (presentationDivisorMonoid (X := X)) where
  base := bottomPoint
  divisorClass :=
    Algebra.GrothendieckAddGroup.of (thetaVZeroLocusEffectiveGlobal X j)

/-- The factor object's divisor class is the actual theta divisor. -/
theorem thetaPilotGlobalFactor_divisorClass
    [Fintype (Bad (nativePlaceSelection X.S))] (j : ProcessionLabel l) :
    (thetaPilotGlobalFactor X j).divisorClass =
      Algebra.GrothendieckAddGroup.of (thetaVZeroLocusEffectiveGlobal X j) := rfl

/-- The actual global Theta-pilot factor family (product over j in F_l^x). -/
structure ThetaPilotGlobalObjectData
    [Fintype (Bad (nativePlaceSelection X.S))] where
  exponentLabel : ProcessionLabel l → Nat
  exponentLabel_eq : exponentLabel = thetaLabelExponent (l := l)
  thetaValue : (j : ProcessionLabel l) →
    (b : Bad (nativePlaceSelection X.S)) →
      CommonPrimeCompletion (K := X.S.arithmetic.F) (nativeBadFPlaceAtPrime X b)
  thetaValue_eq : thetaValue = thetaValueFamily X
  divisorFamily : ProcessionLabel l → EffectiveDivisor (BaseField X)
  divisorFamily_eq : divisorFamily = thetaVZeroLocusEffectiveGlobal X
  factor : ProcessionLabel l →
    Iut.SourceModelFrobenioid.Object (presentationDivisorMonoid (X := X))
  factor_eq : factor = thetaPilotGlobalFactor X

/-- The actual Theta-pilot global factor data from the q_v/theta family and the
global realified Frobenioid presentation. -/
noncomputable def thetaPilotGlobalObjectData
    [Fintype (Bad (nativePlaceSelection X.S))] :
    ThetaPilotGlobalObjectData X where
  exponentLabel := thetaLabelExponent (l := l)
  exponentLabel_eq := rfl
  thetaValue := thetaValueFamily X
  thetaValue_eq := rfl
  divisorFamily := thetaVZeroLocusEffectiveGlobal X
  divisorFamily_eq := rfl
  factor := thetaPilotGlobalFactor X
  factor_eq := rfl

/-- The theta divisor at one label i is the sum over V_bad of the actual theta
zero-locus divisors. -/
theorem thetaVZeroLocusEffectiveGlobal_eq_sum
    [Fintype (Bad (nativePlaceSelection X.S))] (j : ProcessionLabel l) :
    thetaVZeroLocusEffectiveGlobal X j =
      ∑ b : Bad (nativePlaceSelection X.S),
        thetaVZeroLocusEffectiveDivisor X j b := rfl

/-- Projection: the constructed factor's divisor class is the actual global
Theta-pilot divisor. -/
theorem thetaPilotGlobalObjectData_factor_divisorClass
    [Fintype (Bad (nativePlaceSelection X.S))] (j : ProcessionLabel l) :
    ((thetaPilotGlobalObjectData X).factor j).divisorClass =
      Algebra.GrothendieckAddGroup.of
        ((thetaPilotGlobalObjectData X).divisorFamily j) := rfl

end LeanFormal.IUT.XiFPaper.ThetaPilotGlobalObjectActual

end
