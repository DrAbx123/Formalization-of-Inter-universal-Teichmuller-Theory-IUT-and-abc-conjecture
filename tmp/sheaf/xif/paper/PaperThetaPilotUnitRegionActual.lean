import tmp.sheaf.xif.paper.PaperThetaPilotMonoAnalyticNormalizationActual
import tmp.sheaf.xif.paper.GlobalIQHullInterfaceActual

/-! # Paper Theta-pilot unit region: global IQ transport obstruction

GlobalIQHullInterfaceActual supplies the actual global IQ tensor ambient
GlobalIQAmbient C3 j, the actual unit region globalIQUnitRegion C3 j and its
compactness, while PaperThetaPilotCarrierActual supplies the paper F_l^x value
carrier and its actual possible images/hull.

These are different carriers: the global IQ unit region is a subset of the
completion-packet tensor ArithmeticPacketTensor, while the paper Theta-pilot
carrier is F_l^x -> Multiplicative Real.  No actual carrier/place transport,
continuous map, Haar pushforward, or unit-region comparison is constructed in
the tree.

This file records the exact transport data required to build the paper
mono-analytic normalization from the actual global IQ unit region.  It does not
fabricate a transport, a normalized measure, or a normalized log-volume.

No sorry, axiom, True, or PUnit is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperThetaPilotUnitRegionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.GlobalIQHullInterfaceActual
open LeanFormal.IUT.XiFPaper.PaperThetaPilotCarrierActual
open LeanFormal.IUT.XiFPaper.PaperThetaPilotHullLogVolumeActual
open LeanFormal.IUT.XiFPaper.PaperThetaPilotMonoAnalyticNormalizationActual
open MeasureTheory

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [forall i, Fintype (C3.tensorPlaceIndex i)]
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (j : Nat)

/-- Exact missing carrier transport between the global IQ tensor ambient and
the paper F_l^x value carrier, compatible with the possible images/hull and the
Haar unit region. -/
structure PaperGlobalIQCarrierTransport where
  globalToPaper : GlobalIQAmbient (C3 := C3) j -> PaperThetaPilotPoint (l := l)
  paperToGlobal : PaperThetaPilotPoint (l := l) -> GlobalIQAmbient (C3 := C3) j
  left_inv : forall x, paperToGlobal (globalToPaper x) = x
  right_inv : forall y, globalToPaper (paperToGlobal y) = y
  image_compat : Prop
  hull_compat : Prop
  haar_unitRegion_compat : Prop

/-- The exact unit-region transport requirement. -/
def PaperGlobalIQCarrierTransportRequired : Prop :=
  Nonempty (PaperGlobalIQCarrierTransport (C3 := C3) (l := l) j)

/-- The actual global IQ unit region, transported along a hypothetical
transport. -/
noncomputable def transportedGlobalIQUnitRegion
    (M : PaperGlobalIQCarrierTransport (C3 := C3) (l := l) j) :
    Set (PaperThetaPilotPoint (l := l)) :=
  M.globalToPaper '' (globalIQUnitRegion (C3 := C3) j)

/-- Exact required unit-region data on the paper carrier, conditional on the
missing carrier transport and its compactness/measurability/normalization
proofs. -/
structure PaperTransportedGlobalIQUnitRegionData
    (M : PaperGlobalIQCarrierTransport (C3 := C3) (l := l) j) where
  unitRegion : Set (PaperThetaPilotPoint (l := l))
  unitRegion_eq : unitRegion = transportedGlobalIQUnitRegion (C3 := C3) (l := l) j M
  unitRegion_measurable : MeasurableSet unitRegion
  unitRegion_compact : IsCompact unitRegion
  unitRegion_normalized : paperThetaPilotHaar (l := l) unitRegion = 1
  hull_compact : IsCompact
    (actualPaperHullSet (l := l) (T := T) (q := 0))

/-- The exact transported unit-region requirement; no inhabitant is asserted. -/
def PaperTransportedGlobalIQUnitRegionRequired : Prop :=
  Nonempty (Sigma fun M : PaperGlobalIQCarrierTransport (C3 := C3) (l := l) j =>
    PaperTransportedGlobalIQUnitRegionData (C3 := C3) (l := l) j M)

/-- Actual global IQ unit-region compactness is available. -/
theorem globalIQUnitRegion_compact_available :
    IsCompact (globalIQUnitRegion (C3 := C3) j) :=
  globalIQUnitRegion_compact C3 j

/-- Actual paper possible-image set is available. -/
theorem paperPossibleImageSet_available (q : Real) :
    Nonempty (Set (PaperThetaPilotPoint (l := l))) :=
  ⟨paperPossibleImageSet (l := l) q⟩

end LeanFormal.IUT.XiFPaper.PaperThetaPilotUnitRegionActual

end
