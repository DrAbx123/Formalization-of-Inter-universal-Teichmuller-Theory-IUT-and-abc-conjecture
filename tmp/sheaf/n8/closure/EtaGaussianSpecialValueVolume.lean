import tmp.sheaf.n8.closure.T11Native
import tmp.sheaf.n8.closure.SourcePilotRegion
import Mathlib

/-!
# Eta Gaussian special-value volume: exact no-go

The actual completion candidate available in production is

  thetaCompletionActual C3 n j = qUnit ^ (gaussExponent j).toNat,

i.e. the a^(j^2) part, with a := C3.qUnit.  The root-unit factor zeta in
g = zeta * a^(j^2) is not constructed in the completion: production has no
actual theta root-unit lift from the source real theta scale to the completion,
and no tensor-block normalized-volume/determinant formula is supplied.
The exact missing theta value is ThetaPacketIdentification (source real theta
scale = finite theta packet scale).  No arbitrary g is chosen.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open ABCBridge.N8.T11Actual
open ABCBridge.N8.T11Native

namespace LeanFormal.IUT.N8Closure.EtaGaussianSpecialValueVolume

universe ua uv upi umon ui uL

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} [Group Label]
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- Actual a := C3.qUnit in the completion. -/
def actualA : (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) C3.place)ˣ :=
  C3.qUnit

/-- Actual a^(j^2) completion candidate. -/
def actualGaussianPower
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) C3.place :=
  thetaCompletionActual (I := I) C3 n j

/-- The actual completion candidate is the qUnit Gaussian power. -/
theorem actualGaussianPower_eq
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    actualGaussianPower (I := I) C3 n j =
      ((C3.qUnit : (CommonPrimeCompletion
        (K := I.initial.arithmetic.Fmod) C3.place)ˣ) :
        CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) C3.place) ^
        (gaussExponent j.1).toNat := rfl

/-- Exact missing actual theta value: the source real theta scale has no proved
identification with the finite theta packet scale (hence no lift of its root
unit to the completion). -/
def missingActualThetaValue : Prop :=
  ThetaPacketIdentification (I := I) C3

/-! ## Exact no-go for the volume-difference formula

The BPS formula needs:
1. an actual completion g = zeta * a^(j^2), with zeta the source root unit;
2. the actual tensor-block normalized volume/determinant identity.

Only a^(j^2) is constructed (actualGaussianPower); the root unit and the
tensor-block volume formula are absent, and missingActualThetaValue is the
exact source theta identification gap.  No arbitrary g or volume surrogate is
introduced.
-/

end LeanFormal.IUT.N8Closure.EtaGaussianSpecialValueVolume
