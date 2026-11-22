import tmp.sheaf.xif.paper.PaperThetaPilotOnGlobalIQActualAdapted
import tmp.sheaf.xif.paper.C3LogShellTensorHolomorphicHullActual

/-!
# Actual global tensor-packet region: the C3 lambda-O least hull

This file replaces the image-union simplification by the actual least lambda-O
holomorphic hull of the actual C3 tensor log-shell region:

  actualHolomorphicHull C3 (actualUnitRegion C3) = actualUnitRegion C3.

The actual Theta-pilot image set on the global IQ tensor packet is recorded
separately.  Its carrier is the global IQ ambient, while the actual C3 hull
lives on the C3 log-shell tensor block.  The source contract supplies no actual
comparison map between these carriers, so the image-hull landing is the exact
structural gap, not a union fake.

No inequality is asserted.
-/

noncomputable section
open scoped BigOperators
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper
namespace GlobalTensorPacketActualAdapted

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
open LeanFormal.IUT.XiFPaper.PaperThetaPilotOnGlobalIQActualAdapted
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual

universe ua upi umon ui

variable {l : PrimeGeFive}
variable (I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime I.initial.arithmetic.Fmod p)
variable (A : ConcreteC3DonorAssemblyActual (I := I) place)
variable (M : ConcreteC3DonorMissingFields (I := I) place A)
variable [forall i, Fintype
  ((concreteGlobalIQC3 (I := I) place A M).tensorPlaceIndex i)]

/-- The actual concrete C3 used by the global construction. -/
abbrev GlobalConcreteC3 : SourcePilotRegionData (l := l)
    (V := FinitePrimePlace 2 7) (I := I) :=
  concreteGlobalIQC3 (I := I) place A M

/-- The actual C3 log-shell tensor block carrying the lambda-O hull. -/
abbrev GlobalHullBlock : Type :=
  C3LogShellTensorBlock (I := I) (C3 := GlobalConcreteC3 (I := I) place A M)

/-- The actual C3 tensor log-shell unit region O. -/
def GlobalTensorUnitRegion : Set (GlobalHullBlock (I := I) place A M) :=
  actualUnitRegion (C3 := GlobalConcreteC3 (I := I) place A M)

/-- The actual least lambda-O holomorphic hull of the C3 log-shell region. -/
def GlobalThetaPilotTensorRegion : Set (GlobalHullBlock (I := I) place A M) :=
  actualHolomorphicHull (C3 := GlobalConcreteC3 (I := I) place A M)
    (actualUnitRegion (C3 := GlobalConcreteC3 (I := I) place A M))

/-- The actual least lambda-O hull of the C3 log-shell unit region is the unit
region itself. -/
theorem GlobalThetaPilotTensorRegion_eq_unit :
    GlobalThetaPilotTensorRegion (I := I) place A M =
      GlobalTensorUnitRegion (I := I) place A M :=
  actualHolomorphicHull_unitRegion_eq
    (C3 := GlobalConcreteC3 (I := I) place A M)

/-- The actual lambda-O hull region is compact. -/
theorem GlobalThetaPilotTensorRegion_compact :
    IsCompact (GlobalThetaPilotTensorRegion (I := I) place A M) := by
  rw [GlobalThetaPilotTensorRegion_eq_unit]
  exact actualC3LogShellTensorRegion_compact
    (I := I) (C3 := GlobalConcreteC3 (I := I) place A M)

/-- The actual unit region is contained in the actual lambda-O hull. -/
theorem GlobalTensorUnitRegion_subset_region :
    GlobalTensorUnitRegion (I := I) place A M ⊆
      GlobalThetaPilotTensorRegion (I := I) place A M := by
  rw [GlobalThetaPilotTensorRegion_eq_unit]
  exact subset_rfl

/-- Actual Theta-pilot image set on the global IQ tensor packet. -/
abbrev GlobalThetaPilotTensorImage (j : Nat) : Set
    (GlobalIQAmbient (C3 := GlobalConcreteC3 (I := I) place A M) j) :=
  paperThetaPilotPossibleImageSet (I := I) place A M j

/-- The actual finite Theta-pilot image set. -/
theorem GlobalThetaPilotTensorImage_finite (j : Nat) :
    (GlobalThetaPilotTensorImage (I := I) place A M j).Finite :=
  paperThetaPilotPossibleImageSet_finite (I := I) place A M j

/-- Exact structural gap: image carrier vs hull carrier, comparison map, and
image-hull landing. -/
structure GlobalThetaPilotImageHullGap (j : Nat) : Prop where
  globalIQCarrier : Prop
  c3HullCarrier : Prop
  comparisonMap : Prop
  imageLandsInHull : Prop
  imageHullContainment : Prop

/-- Exact required comparison object. -/
def GlobalThetaPilotImageHullGapRequired (j : Nat) : Prop :=
  Nonempty (GlobalThetaPilotImageHullGap (I := I) place A M j)

/-- Actual global tensor-packet region data: the C3 lambda-O least hull, its
unit region and compactness, plus the separately actual finite Theta-pilot
image set on the global IQ ambient. -/
structure GlobalTensorPacketRegionData (j : Nat) where
  region : Set (GlobalHullBlock (I := I) place A M)
  region_eq : region = GlobalThetaPilotTensorRegion (I := I) place A M
  unitRegion : Set (GlobalHullBlock (I := I) place A M)
  unitRegion_eq : unitRegion = GlobalTensorUnitRegion (I := I) place A M
  unitRegion_subset_region : unitRegion ⊆ region
  region_compact : IsCompact region
  image : Set (GlobalIQAmbient (C3 := GlobalConcreteC3 (I := I) place A M) j)
  image_eq : image = GlobalThetaPilotTensorImage (I := I) place A M j
  image_finite : image.Finite
  imageHullGap : Prop
  imageHullGap_eq : imageHullGap =
    GlobalThetaPilotImageHullGapRequired (I := I) place A M j

/-- The actual global tensor-packet region data with the C3 lambda-O hull. -/
noncomputable def globalTensorPacketRegionData (j : Nat) :
    GlobalTensorPacketRegionData (I := I) place A M j where
  region := GlobalThetaPilotTensorRegion (I := I) place A M
  region_eq := rfl
  unitRegion := GlobalTensorUnitRegion (I := I) place A M
  unitRegion_eq := rfl
  unitRegion_subset_region :=
    GlobalTensorUnitRegion_subset_region (I := I) place A M
  region_compact := GlobalThetaPilotTensorRegion_compact (I := I) place A M
  image := GlobalThetaPilotTensorImage (I := I) place A M j
  image_eq := rfl
  image_finite := GlobalThetaPilotTensorImage_finite (I := I) place A M j
  imageHullGap := GlobalThetaPilotImageHullGapRequired (I := I) place A M j
  imageHullGap_eq := rfl

/-- Exact structural gap: no Kummer/Ind action is supplied on the C3 hull
region. -/
structure GlobalTensorPacketKummerIndMissing : Prop where
  kummerAction : Prop
  kummer_action_preserves_region : Prop
  ind1Action : Prop
  ind1_preserves_region : Prop
  ind2Action : Prop
  ind2_preserves_region : Prop
  ind3Action : Prop
  ind3_preserves_region : Prop

/-- Exact missing Kummer/Ind object. -/
def GlobalTensorPacketKummerIndRequired : Prop :=
  Nonempty (GlobalTensorPacketKummerIndMissing (I := I) place A M)

end GlobalTensorPacketActualAdapted
end LeanFormal.IUT.XiFPaper
end
