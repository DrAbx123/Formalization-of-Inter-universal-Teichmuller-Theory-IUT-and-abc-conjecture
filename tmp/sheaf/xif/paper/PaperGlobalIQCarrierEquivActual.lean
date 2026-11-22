import tmp.sheaf.xif.paper.GlobalIQHullInterfaceActual
import tmp.sheaf.xif.paper.PaperThetaPilotCarrierActual
import tmp.sheaf.xif.paper.PaperThetaPilotMonoAnalyticNormalizationActual

/-!
# Global IQ / paper F_l^x carrier equivalence: exact obstruction

The actual global IQ carrier is

  GlobalIQAmbient C3 j = ArithmeticPacketTensor (literalIQPlaces C3 j),

a tensor packet of completion-packet factors indexed by
Fin (j+1) x C3.tensorIndex.  The actual paper Theta-pilot carrier is

  PaperThetaPilotPoint l = (ZMod l.value)^x -> Multiplicative Real,

a function space on F_l^x.  The two carriers have different index structures:
the global IQ carrier is indexed by completion packets and tensor factors, the
paper carrier by F_l^x labels.

No carrier equivalence, place map, continuous map, Haar pushforward, or unit
region transport between them is constructed in the tree.  This file records
the exact required equivalence data and the actual objects that are available;
it does not fabricate an equivalence by choice of basis.

No inequality and no forbidden declaration.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperGlobalIQCarrierEquivActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.GlobalIQHullInterfaceActual
open LeanFormal.IUT.XiFPaper.PaperThetaPilotCarrierActual
open LeanFormal.IUT.XiFPaper.PaperThetaPilotHullLogVolumeActual
open MeasureTheory

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [forall i, Fintype (C3.tensorPlaceIndex i)]
variable (j : Nat)

/-- The actual global IQ carrier at level j. -/
abbrev GlobalIQCarrier : Type :=
  GlobalIQAmbient (C3 := C3) j

/-- The actual paper F_l^x carrier. -/
abbrev PaperCarrier : Type :=
  PaperThetaPilotPoint (l := l)

/-- Exact required carrier equivalence and unit-region/Haar compatibility.

The paper unit region is an output field, not a fabricated box: it must be the
image of the actual global IQ unit region under the carrier equivalence, and it
must be compact.  The Haar pushforward and hull compatibility are exact source
conditions left as propositions. -/
structure PaperGlobalIQCarrierEquivData where
  equiv : GlobalIQCarrier (C3 := C3) j ≃ PaperCarrier (l := l)
  paperUnitRegion : Set (PaperCarrier (l := l))
  unitRegion_image :
    equiv '' (globalIQUnitRegion (C3 := C3) j) = paperUnitRegion
  paperUnitRegion_compact : IsCompact paperUnitRegion
  haar_pushforward_compat : Prop
  hull_compat : Prop

/-- The exact carrier-equivalence requirement. -/
def PaperGlobalIQCarrierEquivRequired : Prop :=
  Nonempty (PaperGlobalIQCarrierEquivData (C3 := C3) (l := l) j)

/-- The actual global IQ unit region is compact. -/
theorem globalIQCarrier_unitRegion_compact :
    IsCompact (globalIQUnitRegion (C3 := C3) j) :=
  globalIQUnitRegion_compact C3 j

/-- The actual global IQ carrier and unit region exist. -/
theorem globalIQCarrier_available :
    Nonempty (GlobalIQCarrier (C3 := C3) j) :=
  ⟨(0 : GlobalIQCarrier (C3 := C3) j)⟩

/-- The actual paper carrier exists. -/
theorem paperCarrier_available :
    Nonempty (PaperCarrier (l := l)) :=
  ⟨fun _ => Multiplicative.ofAdd 0⟩

/-- Exact obstruction: the carrier equivalence and unit-region transport are
not constructed; the requirement is exactly the nonempty structure above. -/
theorem paperGlobalIQCarrierEquiv_obstruction_iff :
    PaperGlobalIQCarrierEquivRequired (C3 := C3) (l := l) j ↔
      Nonempty (PaperGlobalIQCarrierEquivData (C3 := C3) (l := l) j) :=
  Iff.rfl

/-- The actual available part: both carriers and the actual global IQ unit
region with compactness.  The missing part is the equivalence/transport. -/
theorem paperGlobalIQCarrierEquiv_available_part :
    Nonempty (GlobalIQCarrier (C3 := C3) j)
      ∧ Nonempty (PaperCarrier (l := l))
      ∧ IsCompact (globalIQUnitRegion (C3 := C3) j) :=
  ⟨globalIQCarrier_available (C3 := C3) (j := j),
    paperCarrier_available (l := l),
    globalIQCarrier_unitRegion_compact (C3 := C3) (j := j)⟩

end LeanFormal.IUT.XiFPaper.PaperGlobalIQCarrierEquivActual

end
