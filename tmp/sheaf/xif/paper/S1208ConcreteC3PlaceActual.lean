import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion

/-! # S1208: concrete C3 place/index data for V = FinitePrimePlace 2 7

The concrete source place type is `FinitePrimePlace 2 7`.  This file constructs
the actual two fields of a candidate `PrimeStripC3PlaceComparison` that do not
need a C3 object: the identity index equivalence and the constant strip place
coming from the supplied actual finite place.

No weak interface is introduced.  Assembling a full
`PrimeStripC3PlaceComparison` still needs an actual `SourcePilotRegionData C3`
with `C3.tensorIndex = FinitePrimePlace 2 7` and matching `tensorPlaces`; the
concrete C3 donor is blocked at `SourcePilotRegionDonors` roots/Kummer/tensor
landing (see `ConcreteC3DonorActual`/`ConcreteC3DonorCompletionActual`), so the
first missing object is the C3 donor field, not these two maps. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1208ConcreteC3PlaceActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace

universe ua upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

/-- Actual index equivalence for the concrete place type: identity. -/
noncomputable def concreteC3IndexEquiv :
    FinitePrimePlace 2 7 ≃ FinitePrimePlace 2 7 :=
  Equiv.refl (FinitePrimePlace 2 7)

@[simp] theorem concreteC3IndexEquiv_apply
    (v : FinitePrimePlace 2 7) :
    concreteC3IndexEquiv v = v := rfl

/-- Actual strip-place map: the constant supplied finite place. -/
noncomputable def concreteC3StripPlace :
    FinitePrimePlace 2 7 →
      FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p :=
  fun _ => place

@[simp] theorem concreteC3StripPlace_apply
    (v : FinitePrimePlace 2 7) :
    concreteC3StripPlace I place v = place := rfl

/-- Both constructed fields are actual and nonempty (the index equivalence is
bijective; the strip place is the supplied actual place). -/
theorem concreteC3IndexPlace_actual :
    Function.Bijective (concreteC3IndexEquiv) ∧
      ∀ v : FinitePrimePlace 2 7,
        concreteC3StripPlace I place v = place :=
  ⟨Equiv.bijective concreteC3IndexEquiv,
    fun _ => rfl⟩

#check concreteC3IndexEquiv
#check concreteC3StripPlace
#check concreteC3IndexPlace_actual

end LeanFormal.IUT.XiFPaper.S1208ConcreteC3PlaceActual
end
