import tmp.sheaf.xif.paper.GlobalIQHullThetaPilotActualAdapted

/-!
# Transport of the global Theta-pilot image/hull into the IQ ambient

The actual global Theta-pilot candidate from GlobalIQHullThetaPilotActualAdapted lives
in the product carrier

  (v : V) -> I.ThetaPilotPoint v,

while the global IQ hull ambient is the actual tensor packet

  LiteralIQAmbient C3 j = ArithmeticPacketTensor (literalIQPlaces C3 j).

The two carriers are different.  What is missing is an actual multiradial
transport/embedding

  embed : ((v : V) -> I.ThetaPilotPoint v) -> ArithmeticPacketTensor ...

together with its compatibility with the actual image/hull sets.

This file constructs the actual transport of the image/hull sets once such an
embedding is supplied, and records the exact embedding obstruction.  It does not
insert any Theta-pilot point into the tensor ambient by fiat.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.GlobalThetaPilotIQEmbeddingActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.ThetaPilotObjectActual
open LeanFormal.IUT.XiFPaper.GlobalIQHullThetaPilotActualAdapted
open LeanFormal.IUT.XiFPaper.GlobalIQHullInterfaceActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [forall i, Fintype (C3.tensorPlaceIndex i)]
variable (j : Nat)
variable (R : ∀ v : V, I.SourceImageRealization v)
variable (n : ThetaPilotCarrier l)

/-- Exact missing global multiradial embedding from the product Theta-pilot
carrier into the global IQ tensor ambient. -/
structure GlobalThetaPilotIQEmbeddingData where
  embed : GlobalThetaPilotCarrier (I := I) → GlobalIQAmbient (C3 := C3) j

/-- The actual image set transported along a supplied embedding. -/
def transportedImageSet
    (E : GlobalThetaPilotIQEmbeddingData (I := I) C3 j) :
    Set (GlobalIQAmbient (C3 := C3) j) :=
  E.embed '' globalThetaPilotImageSet (I := I) R n

/-- The actual hull transported along a supplied embedding. -/
def transportedHull
    (E : GlobalThetaPilotIQEmbeddingData (I := I) C3 j) :
    Set (GlobalIQAmbient (C3 := C3) j) :=
  E.embed '' globalThetaPilotHull (I := I) R n

/-- The transported image is contained in the transported hull. -/
theorem transportedImageSet_subset_transportedHull
    (E : GlobalThetaPilotIQEmbeddingData (I := I) C3 j) :
    transportedImageSet (I := I) C3 j R n E ⊆
      transportedHull (I := I) C3 j R n E := by
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, globalThetaPilotImageSet_subset_hull (I := I) R n hx, rfl⟩

/-- Actual transported image/hull data from a supplied global multiradial
embedding. -/
structure GlobalThetaPilotIQTransportActual where
  embed : GlobalThetaPilotCarrier (I := I) → GlobalIQAmbient (C3 := C3) j
  imageSet : Set (GlobalIQAmbient (C3 := C3) j)
  hull : Set (GlobalIQAmbient (C3 := C3) j)
  imageSet_eq : imageSet = embed '' globalThetaPilotImageSet (I := I) R n
  hull_eq : hull = embed '' globalThetaPilotHull (I := I) R n
  imageSet_subset_hull : imageSet ⊆ hull

/-- The actual transport data constructed from an explicit global embedding. -/
noncomputable def globalThetaPilotIQTransportActual
    (E : GlobalThetaPilotIQEmbeddingData (I := I) C3 j) :
    GlobalThetaPilotIQTransportActual (I := I) C3 j R n where
  embed := E.embed
  imageSet := transportedImageSet (I := I) C3 j R n E
  hull := transportedHull (I := I) C3 j R n E
  imageSet_eq := rfl
  hull_eq := rfl
  imageSet_subset_hull :=
    transportedImageSet_subset_transportedHull (I := I) C3 j R n E

/-- The transport image is the transported source image. -/
theorem globalThetaPilotIQTransportActual_imageSet
    (E : GlobalThetaPilotIQEmbeddingData (I := I) C3 j) :
    (globalThetaPilotIQTransportActual (I := I) C3 j R n E).imageSet =
      E.embed '' globalThetaPilotImageSet (I := I) R n := rfl

/-- The transport hull is the transported source hull. -/
theorem globalThetaPilotIQTransportActual_hull
    (E : GlobalThetaPilotIQEmbeddingData (I := I) C3 j) :
    (globalThetaPilotIQTransportActual (I := I) C3 j R n E).hull =
      E.embed '' globalThetaPilotHull (I := I) R n := rfl

/-- Exact obstruction: the global Theta-pilot carrier has no actual embedding
into the global IQ tensor ambient supplied by the current source data. -/
def GlobalThetaPilotIQEmbeddingObstruction : Prop :=
  Nonempty (GlobalThetaPilotIQEmbeddingData (I := I) C3 j)

/-- The embedding obstruction is exactly the missing global multiradial map. -/
theorem GlobalThetaPilotIQEmbeddingObstruction_iff :
    GlobalThetaPilotIQEmbeddingObstruction (I := I) C3 j ↔
      Nonempty (GlobalThetaPilotIQEmbeddingData (I := I) C3 j) :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.GlobalThetaPilotIQEmbeddingActualAdapted

end
