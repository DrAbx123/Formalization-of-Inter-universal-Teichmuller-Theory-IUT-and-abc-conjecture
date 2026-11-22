import tmp.sheaf.xif.paper.C3PlaceTensorWitnessActualAdapted
import tmp.sheaf.xif.paper.GlobalThetaPilotKummerActualAdapted
import tmp.sheaf.xif.paper.ThetaPilotQImagePartialActualAdapted
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticIQTensor

/-!
# Concrete completion image to literal IQ ambient

ConcreteC3DonorCompletionActual supplies the actual tensor places

  concreteTensorPlaces I place i () = place

with tensorIndex = FinitePrimePlace 2 7 and tensorPlaceIndex = Unit.
C3PlaceTensorWitnessActualAdapted supplies the actual rfl place-tensor witness.

This file constructs the concrete literal IQ ambient on the tensor index
Fin(j+1) x ConcreteTensorIndex and the actual completion-image map

  concreteThetaImage idx = concreteQUnit^(gauss exponent)
  concreteCompletionImageToLiteralIQ idx = tensor of concreteThetaImage idx
    in every factor of the concrete literal IQ ambient.

The map is actual: every tensor factor is the same concrete completion, and the
factor element is the actual qUnit power in its CompletionPacket.  The image set
is finite.

Exact obstacle: the log-Kummer compatibility of this tensor map with the actual
SourceTimesMuKummerLayer is not constructed; it requires a multiradial action of
the Kummer group on the literal IQ tensor packet, which is not in the current
tree.  No compatibility is faked.

No empty type, no True/PUnit/axiom/sorry, no inequality.  WRITE-ONLY; no local
compile; queued.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.ConcreteCompletionImageToLiteralIQActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorCompletionActual
open LeanFormal.IUT.XiFPaper.C3PlaceTensorWitnessActualAdapted
open LeanFormal.IUT.XiFPaper.ThetaPilotQImagePartialActualAdapted
open LeanFormal.IUT.NumberFieldFinitePlace

universe ua upi umon ui

variable {l : PrimeGeFive}
variable (I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

/-- The concrete literal IQ index at level j. -/
abbrev ConcreteLiteralIQIndex (j : Nat) : Type :=
  Fin (j + 1) × ConcreteTensorIndex

/-- The concrete literal IQ place index. -/
abbrev ConcreteLiteralIQPlaceIndex
    (j : Nat) (x : ConcreteLiteralIQIndex j) : Type :=
  ConcreteTensorPlaceIndex x.2

/-- The concrete literal IQ places: constant concrete tensor place. -/
noncomputable def concreteLiteralIQPlaces
    (j : Nat) (x : ConcreteLiteralIQIndex j)
    (a : ConcreteLiteralIQPlaceIndex j x) :
    FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p :=
  concreteTensorPlaces (I := I) place x.2 a

/-- The concrete literal IQ ambient tensor packet. -/
abbrev ConcreteLiteralIQAmbient (j : Nat) : Type :=
  ArithmeticPacketTensor (concreteLiteralIQPlaces I place j)

/-- The actual completion image at a Theta-pilot index. -/
noncomputable def concreteThetaImage
    (idx : ThetaPilotImageIndex (l := l)) :
    (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)ˣ :=
  concreteQUnit I place ^ thetaImageExponent (l := l) idx

/-- The actual completion image is the qUnit power. -/
theorem concreteThetaImage_eq
    (idx : ThetaPilotImageIndex (l := l)) :
    concreteThetaImage I place idx =
      concreteQUnit I place ^ thetaImageExponent (l := l) idx := rfl

/-- The actual tensor embedding of a completion unit into the concrete literal
IQ ambient: put the same unit in every tensor factor. -/
noncomputable def completionUnitToConcreteLiteralIQ
    (j : Nat)
    (u : (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)ˣ) :
    ConcreteLiteralIQAmbient I place j :=
  PiTensorProduct.tprod ℚ_[p]
    (fun x : ConcreteLiteralIQIndex j =>
      fun _ : ConcreteLiteralIQPlaceIndex j x =>
        (u : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place))

/-- The actual concrete completion-image map into the literal IQ ambient. -/
noncomputable def concreteCompletionImageToLiteralIQ
    (j : Nat) (idx : ThetaPilotImageIndex (l := l)) :
    ConcreteLiteralIQAmbient I place j :=
  completionUnitToConcreteLiteralIQ I place j (concreteThetaImage I place idx)

/-- The actual concrete literal IQ image set. -/
def concreteLiteralIQImageSet (j : Nat) :
    Set (ConcreteLiteralIQAmbient I place j) :=
  Set.range (concreteCompletionImageToLiteralIQ I place j)

/-- The concrete literal IQ image set is finite. -/
theorem concreteLiteralIQImageSet_finite (j : Nat) :
    (concreteLiteralIQImageSet I place j).Finite :=
  Set.finite_range _

/-- The selected concrete tensor place is exactly the supplied place; this is
the C3PlaceTensorWitnessActualAdapted rfl witness used by the ambient construction. -/
theorem concreteLiteralIQPlaces_selected
    (j : Nat) :
    concreteLiteralIQPlaces I place j
        (⟨0, Nat.succ_pos j⟩, (concreteC3PlaceTensorWitness I place).i)
        (concreteC3PlaceTensorWitness I place).a = place := rfl

/-- The actual concrete completion image to literal IQ data. -/
structure ConcreteCompletionImageToLiteralIQData where
  index : Type
  ambient : Nat → Type
  completionImage :
    ThetaPilotImageIndex (l := l) →
      (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)ˣ
  literalIQImage :
    (j : Nat) → ThetaPilotImageIndex (l := l) →
      ConcreteLiteralIQAmbient I place j
  imageSet : (j : Nat) → Set (ConcreteLiteralIQAmbient I place j)
  index_eq : index = ThetaPilotImageIndex (l := l)
  ambient_eq : ambient = ConcreteLiteralIQAmbient I place
  completionImage_eq : completionImage = concreteThetaImage I place
  literalIQImage_eq :
    literalIQImage = concreteCompletionImageToLiteralIQ I place
  imageSet_eq : imageSet = concreteLiteralIQImageSet I place

/-- The actual concrete completion-image-to-literal-IQ data. -/
noncomputable def concreteCompletionImageToLiteralIQData :
    ConcreteCompletionImageToLiteralIQData I place where
  index := ThetaPilotImageIndex (l := l)
  ambient := ConcreteLiteralIQAmbient I place
  completionImage := concreteThetaImage I place
  literalIQImage := concreteCompletionImageToLiteralIQ I place
  imageSet := concreteLiteralIQImageSet I place
  index_eq := rfl
  ambient_eq := rfl
  completionImage_eq := rfl
  literalIQImage_eq := rfl
  imageSet_eq := rfl

/-- The completion image projection. -/
theorem concreteCompletionImageToLiteralIQData_completionImage
    (idx : ThetaPilotImageIndex (l := l)) :
    (concreteCompletionImageToLiteralIQData I place).completionImage idx =
      concreteThetaImage I place idx := rfl

/-- The literal IQ image projection. -/
theorem concreteCompletionImageToLiteralIQData_literalIQImage
    (j : Nat) (idx : ThetaPilotImageIndex (l := l)) :
    (concreteCompletionImageToLiteralIQData I place).literalIQImage j idx =
      concreteCompletionImageToLiteralIQ I place j idx := rfl

/-- The literal IQ image set projection. -/
theorem concreteCompletionImageToLiteralIQData_imageSet
    (j : Nat) :
    (concreteCompletionImageToLiteralIQData I place).imageSet j =
      concreteLiteralIQImageSet I place j := rfl

end LeanFormal.IUT.XiFPaper.ConcreteCompletionImageToLiteralIQActualAdapted
