import tmp.sheaf.xif.paper.PaperThetaPilotOnGlobalIQActual
import tmp.sheaf.xif.paper.C3LogShellTensorHolomorphicHullActual

/-! # Paper Theta-pilot hull on the global IQ ambient

PaperThetaPilotOnGlobalIQActual supplies the actual finite possible-image set

  imageSet j subset GlobalIQAmbient C3 j

on the global IQ tensor ambient.  C3LogShellTensorHolomorphicHullActual supplies
the actual lambda*O scaled regions and the literal least lambda*O hull on the
tensor log-shell block

  C3LogShellTensorBlock C3 = ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple.

These are different carriers:

  GlobalIQAmbient C3 j = ArithmeticPacketTensor (literalIQPlaces C3 j),

while C3LogShellTensorBlock C3 is a single tuple block, not the packet tensor.
No identity between them is asserted or fabricated here.

This file therefore constructs the global IQ Theta-pilot hull conditionally on
an actual carrier transport

  toBlock : GlobalIQAmbient C3 j -> C3LogShellTensorBlock C3

which sends the actual imageSet into the block region and whose actual
lambda*O least hull carries the actual compactness and unit-region containment.
Given such a transport the global hull is the preimage of the actual least hull,
image_subset_hull is proved, and the hull data are packaged.  The exact missing
carrier transport is recorded as an obstruction; no hull is fabricated.

No raw log, no F_l^x function-space carrier, no inequality, no sorry/axiom. -/

noncomputable section
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperThetaPilotHullOnGlobalIQActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorCompletionActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorAssemblyActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.PaperThetaPilotOnGlobalIQActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.GlobalIQHullInterfaceActual

universe ua upi umon ui

variable {l : PrimeGeFive}
variable (I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
variable (A : ConcreteC3DonorAssemblyActual (I := I) place)
variable (M : ConcreteC3DonorMissingFields (I := I) place A)
variable (j : Nat)

/-- The actual concrete C3 used for the global IQ image and the log-shell block. -/
abbrev hullC3 : SourcePilotRegionData (l := l) (V := FinitePrimePlace 2 7) (I := I) :=
  concreteGlobalIQC3 (I := I) place A M

/-- The global IQ ambient carrying the actual possible images. -/
abbrev GlobalIQImageCarrier : Type :=
  GlobalIQAmbient (C3 := hullC3 (I := I) place A M) j

/-- The actual C3 log-shell tensor block carrying the lambda*O hull. -/
abbrev GlobalIQHullBlock : Type :=
  C3LogShellTensorBlock (I := I) (hullC3 (I := I) place A M)

/-- The actual possible-image set on the global IQ ambient. -/
abbrev globalIQImageSet : Set (GlobalIQImageCarrier (I := I) place A M j) :=
  paperThetaPilotPossibleImageSet (I := I) place A M j

/-- Actual carrier transport data from the global IQ ambient to the C3 log-shell
block, preserving the actual image set and carrying the actual compact hull with
its unit-region containment. -/
structure GlobalIQThetaPilotHullTransport where
  toBlock : GlobalIQImageCarrier (I := I) place A M j →
    GlobalIQHullBlock (I := I) place A M
  imageRegion : Set (GlobalIQHullBlock (I := I) place A M)
  imageRegion_eq :
    imageRegion = toBlock '' globalIQImageSet (I := I) place A M j
  hullBlock : Set (GlobalIQHullBlock (I := I) place A M)
  hullBlock_eq :
    hullBlock = actualHolomorphicHull (I := I) (hullC3 (I := I) place A M)
      imageRegion
  hullBlock_compact : IsCompact hullBlock
  hullBlock_subset_unitRegion :
    hullBlock ⊆ actualUnitRegion (I := I) (hullC3 (I := I) place A M)

/-- The actual global IQ hull obtained as the preimage of the transported
least lambda*O hull. -/
def globalIQHull
    (E : GlobalIQThetaPilotHullTransport (I := I) place A M j) :
    Set (GlobalIQImageCarrier (I := I) place A M j) :=
  E.toBlock ⁻¹' E.hullBlock

/-- The actual possible-image set is contained in the global IQ hull. -/
theorem globalIQImageSet_subset_hull
    (E : GlobalIQThetaPilotHullTransport (I := I) place A M j) :
    globalIQImageSet (I := I) place A M j ⊆
      globalIQHull (I := I) place A M j E := by
  intro x hx
  have hxRegion : E.toBlock x ∈ E.imageRegion := by
    rw [E.imageRegion_eq]
    exact ⟨x, hx, rfl⟩
  have hxHull : E.toBlock x ∈ E.hullBlock := by
    rw [E.hullBlock_eq]
    exact actualRegion_subset_hull (I := I)
      (hullC3 (I := I) place A M) E.imageRegion hxRegion
  exact hxHull

/-- The actual compactness of the transported block hull. -/
theorem globalIQHullBlock_compact
    (E : GlobalIQThetaPilotHullTransport (I := I) place A M j) :
    IsCompact E.hullBlock :=
  E.hullBlock_compact

/-- The transported block hull is contained in the actual C3 log-shell unit
region. -/
theorem globalIQHullBlock_subset_unitRegion
    (E : GlobalIQThetaPilotHullTransport (I := I) place A M j) :
    E.hullBlock ⊆ actualUnitRegion (I := I) (hullC3 (I := I) place A M) :=
  E.hullBlock_subset_unitRegion

/-- Actual global IQ Theta-pilot hull data constructed from a supplied carrier
transport. -/
structure PaperThetaPilotHullOnGlobalIQData
    (E : GlobalIQThetaPilotHullTransport (I := I) place A M j) where
  hull : Set (GlobalIQImageCarrier (I := I) place A M j)
  hull_eq : hull = globalIQHull (I := I) place A M j E
  image_subset_hull :
    globalIQImageSet (I := I) place A M j ⊆ hull
  blockHull : Set (GlobalIQHullBlock (I := I) place A M)
  blockHull_eq : blockHull = E.hullBlock
  blockHull_compact : IsCompact blockHull
  blockHull_subset_unitRegion :
    blockHull ⊆ actualUnitRegion (I := I) (hullC3 (I := I) place A M)

/-- The actual global IQ hull data from an explicit carrier transport. -/
def paperThetaPilotHullOnGlobalIQData
    (E : GlobalIQThetaPilotHullTransport (I := I) place A M j) :
    PaperThetaPilotHullOnGlobalIQData (I := I) place A M j E where
  hull := globalIQHull (I := I) place A M j E
  hull_eq := rfl
  image_subset_hull := globalIQImageSet_subset_hull (I := I) place A M j E
  blockHull := E.hullBlock
  blockHull_eq := rfl
  blockHull_compact := E.hullBlock_compact
  blockHull_subset_unitRegion := E.hullBlock_subset_unitRegion

/-- Exact carrier-type obstruction: GlobalIQAmbient C3 j is an
ArithmeticPacketTensor, while C3LogShellTensorBlock C3 is an
ArithmeticTensorTupleBlock; no actual transport is supplied by the current
source data. -/
def GlobalIQThetaPilotHullCarrierObstruction : Prop :=
  Nonempty (GlobalIQThetaPilotHullTransport (I := I) place A M j)
end LeanFormal.IUT.XiFPaper.PaperThetaPilotHullOnGlobalIQActual

end
