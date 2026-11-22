import tmp.sheaf.xif.paper.ConcreteC3DonorAssemblyActual
import tmp.sheaf.xif.paper.ConcreteCompletionImageToLiteralIQActual
import tmp.sheaf.xif.paper.GlobalIQHullInterfaceActual

/-! # Paper Theta-pilot possible images on the global IQ ambient

The global IQ ambient is the actual tensor packet

  GlobalIQAmbient C3 j = LiteralIQAmbient C3 j
                       = ArithmeticPacketTensor (literalIQPlaces C3 j).

This file constructs the actual Theta-pilot possible-image set directly on that
ambient, using the actual concrete completion-image map

  concreteCompletionImageToLiteralIQ I place j idx
    = tensor of (concreteQUnit I place)^(gauss exponent idx)

in every tensor factor.

The concrete C3 is assembled from the actual concrete C3 donor fields and the
explicit remaining donor fields; its tensor data are exactly the concrete
tensor data, so the literal IQ ambient is the concrete literal IQ ambient
without introducing any carrier equivalence or F_l^x function-space carrier.
The image set is finite.

The global Theta-pilot hull itself is not supplied by the tensor ambient alone;
the exact missing hull/scaling data is recorded by the existing
GlobalIQHullMissingFields obstruction.  No raw log and no fake inequality.

No True/PUnit/axiom/sorry. -/

noncomputable section
open scoped BigOperators
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperThetaPilotOnGlobalIQActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorCompletionActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorAssemblyActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.ConcreteCompletionImageToLiteralIQActual
open LeanFormal.IUT.XiFPaper.GlobalIQHullInterfaceActual
open LeanFormal.IUT.XiFPaper.LiteralIQCarrierConstruction

universe ua upi umon ui

variable {l : PrimeGeFive}
variable (I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

/-- The actual concrete C3 assembled from the concrete donor fields plus the
explicit remaining donor fields. -/
noncomputable def concreteGlobalIQC3
    (A : ConcreteC3DonorAssemblyActual (I := I) place)
    (M : ConcreteC3DonorMissingFields (I := I) place A) :
    SourcePilotRegionData (l := l) (V := FinitePrimePlace 2 7) (I := I) :=
  sourcePilotRegionDataOfDonors
    (toSourcePilotRegionDonors (I := I) place A M)

/-- The concrete global IQ ambient at level j. -/
abbrev ConcreteGlobalIQAmbient
    (A : ConcreteC3DonorAssemblyActual (I := I) place)
    (M : ConcreteC3DonorMissingFields (I := I) place A)
    (j : Nat) : Type :=
  GlobalIQAmbient (C3 := concreteGlobalIQC3 (I := I) place A M) j

/-- Actual Theta-pilot possible image at index idx in the global IQ ambient:
the tensor of the actual qUnit^(gauss exponent) completion unit in every factor. -/
noncomputable def paperThetaPilotPossibleImage
    (A : ConcreteC3DonorAssemblyActual (I := I) place)
    (M : ConcreteC3DonorMissingFields (I := I) place A)
    (j : Nat) (idx : ThetaPilotImageIndex (l := l)) :
    ConcreteGlobalIQAmbient (I := I) place A M j :=
  concreteCompletionImageToLiteralIQ (I := I) place j idx

/-- Actual Theta-pilot possible-image set on the global IQ ambient. -/
def paperThetaPilotPossibleImageSet
    (A : ConcreteC3DonorAssemblyActual (I := I) place)
    (M : ConcreteC3DonorMissingFields (I := I) place A)
    (j : Nat) :
    Set (ConcreteGlobalIQAmbient (I := I) place A M j) :=
  Set.range (paperThetaPilotPossibleImage (I := I) place A M j)

/-- The actual possible-image set is finite. -/
theorem paperThetaPilotPossibleImageSet_finite
    (A : ConcreteC3DonorAssemblyActual (I := I) place)
    (M : ConcreteC3DonorMissingFields (I := I) place A)
    (j : Nat) :
    (paperThetaPilotPossibleImageSet (I := I) place A M j).Finite :=
  Set.finite_range _

/-- Actual possible-image data on the global IQ ambient. -/
structure PaperThetaPilotPossibleImageData where
  C3 : SourcePilotRegionData (l := l) (V := FinitePrimePlace 2 7) (I := I)
  level : Nat
  imageMap :
    ThetaPilotImageIndex (l := l) →
      GlobalIQAmbient (C3 := C3) level
  imageSet : Set (GlobalIQAmbient (C3 := C3) level)
  imageSet_eq : imageSet = Set.range imageMap
  imageSet_finite : imageSet.Finite

/-- The actual possible-image data constructed from the concrete completion
images on the global IQ ambient. -/
noncomputable def paperThetaPilotPossibleImageData
    (A : ConcreteC3DonorAssemblyActual (I := I) place)
    (M : ConcreteC3DonorMissingFields (I := I) place A)
    (j : Nat) :
    PaperThetaPilotPossibleImageData (I := I) place where
  C3 := concreteGlobalIQC3 (I := I) place A M
  level := j
  imageMap := paperThetaPilotPossibleImage (I := I) place A M j
  imageSet := paperThetaPilotPossibleImageSet (I := I) place A M j
  imageSet_eq := rfl
  imageSet_finite := paperThetaPilotPossibleImageSet_finite (I := I) place A M j

/-- The possible-image projection at index idx. -/
theorem paperThetaPilotPossibleImageData_imageMap
    (A : ConcreteC3DonorAssemblyActual (I := I) place)
    (M : ConcreteC3DonorMissingFields (I := I) place A)
    (j : Nat) (idx : ThetaPilotImageIndex (l := l)) :
    (paperThetaPilotPossibleImageData (I := I) place A M j).imageMap idx =
      concreteCompletionImageToLiteralIQ (I := I) place j idx := rfl

/-- Exact missing global Theta-pilot hull/scaling data on the global IQ ambient:
the tensor ambient alone does not supply the image hull or lambda-scaling. -/
def PaperThetaPilotGlobalIQHullObstruction
    (A : ConcreteC3DonorAssemblyActual (I := I) place)
    (M : ConcreteC3DonorMissingFields (I := I) place A)
    (j : Nat) : Prop :=
  GlobalIQHullInterfaceObstruction
    (C3 := concreteGlobalIQC3 (I := I) place A M) j

end LeanFormal.IUT.XiFPaper.PaperThetaPilotOnGlobalIQActual

end
