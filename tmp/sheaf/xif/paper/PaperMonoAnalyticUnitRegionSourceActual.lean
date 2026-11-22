import tmp.sheaf.xif.paper.GlobalIQHullInterfaceActual
import tmp.sheaf.xif.paper.PaperThetaPilotMonoAnalyticNormalizationActual
import tmp.sheaf.xif.paper.C3LogShellTensorHolomorphicHullActual

/-!
# Paper mono-analytic unit region from the actual source O: obstruction

This file starts from the actual source mono-analytic unit regions available in
the tree:

* the global IQ tensor unit region globalIQUnitRegion C3 j, with its actual
  additive Haar measure globalIQHaar C3 j, its actual compactness, and its
  actual log-volume;
* the C3 log-shell tensor unit region actualUnitRegion, with its actual
  compactness and actual lambda-O holomorphic hull.

These are source mono-analytic unit regions, not arbitrary boxes.  The paper
Theta-pilot carrier is the different F_l^x -> Multiplicative Real value carrier.
No carrier equivalence, continuous map, Haar pushforward, or unit-region
transport between these carriers is constructed in the tree.

This file constructs the actual SourceMonoAnalyticO data and the exact
transport requirement for the paper unit region.  It deliberately does not use
the [0,1] log-coordinate box and does not fake a paper normalized unit region.
No inequality and no forbidden declaration.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperMonoAnalyticUnitRegionSourceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.GlobalIQHullInterfaceActual
open LeanFormal.IUT.XiFPaper.PaperThetaPilotCarrierActual
open LeanFormal.IUT.XiFPaper.PaperThetaPilotHullLogVolumeActual
open LeanFormal.IUT.XiFPaper.PaperThetaPilotMonoAnalyticNormalizationActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open MeasureTheory

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [forall i, Fintype (C3.tensorPlaceIndex i)]
variable (j : Nat)

/-- Actual source mono-analytic O data available in the tree: a carrier, a
compact unit region, and an actual additive Haar measure on the carrier. -/
structure SourceMonoAnalyticO where
  carrier : Type
  unitRegion : Set carrier
  unitRegion_compact : IsCompact unitRegion
  haar : Measure carrier
  haar_isAddHaar : Measure.IsAddHaarMeasure haar

/-- Actual source O from the global IQ tensor ambient. -/
noncomputable def sourceMonoAnalyticO_globalIQ :
    SourceMonoAnalyticO (C3 := C3) (l := l) :=
  { carrier := GlobalIQAmbient (C3 := C3) j
    unitRegion := globalIQUnitRegion (C3 := C3) j
    unitRegion_compact := globalIQUnitRegion_compact C3 j
    haar := globalIQHaar C3 j
    haar_isAddHaar := globalIQHaar_isAddHaar C3 j }

/-- Actual source O from the C3 log-shell tensor packet. -/
noncomputable def sourceMonoAnalyticO_c3LogShell :
    Set (HullBlock (I := I) C3) :=
  actualUnitRegion (I := I) C3

/-- Actual compactness of the C3 log-shell tensor source O. -/
theorem sourceMonoAnalyticO_c3LogShell_compact :
    IsCompact (sourceMonoAnalyticO_c3LogShell (I := I) C3) :=
  actualC3LogShellTensorRegion_compact (I := I) C3

/-- Actual global IQ unit region is compact. -/
theorem sourceGlobalIQUnitRegion_compact :
    IsCompact (globalIQUnitRegion (C3 := C3) j) :=
  globalIQUnitRegion_compact C3 j

/-- Exact transport required from the actual global IQ source O to the paper
F_l^x value carrier.  This is the missing mono-analytic unit-region transport;
no such transport is constructed in the tree. -/
structure PaperGlobalIQUnitRegionTransport where
  source : SourceMonoAnalyticO (C3 := C3) (l := l)
  paperUnitRegion : Set (PaperThetaPilotPoint (l := l))
  carrierEquiv : source.carrier ≃ PaperThetaPilotPoint (l := l)
  unitRegion_image : carrierEquiv '' source.unitRegion = paperUnitRegion
  unitRegion_compact : IsCompact paperUnitRegion
  haar_pushforward_compat : Prop
  hull_compat : Prop

/-- The exact paper unit-region transport requirement. -/
def PaperGlobalIQUnitRegionTransportRequired : Prop :=
  Nonempty (PaperGlobalIQUnitRegionTransport (C3 := C3) (l := l) j)

/-- Actual source O data exists (global IQ and C3 log-shell). -/
theorem sourceMonoAnalyticO_available :
    Nonempty (SourceMonoAnalyticO (C3 := C3) (l := l))
      ∧ IsCompact (sourceMonoAnalyticO_c3LogShell (I := I) C3) :=
  ⟨⟨sourceMonoAnalyticO_globalIQ (C3 := C3) (l := l) (j := j)⟩,
    sourceMonoAnalyticO_c3LogShell_compact (I := I) C3⟩

/-- The paper unit region is exactly a transported actual source unit region,
not an arbitrary log-coordinate box. -/
def PaperUnitRegionFromSource : Prop :=
  PaperGlobalIQUnitRegionTransportRequired (C3 := C3) (l := l) j

/-- Exact obstruction: the actual source O is available, but its transport to
the paper carrier is the missing data. -/
theorem paperUnitRegionFromSource_obstruction_iff :
    PaperUnitRegionFromSource (C3 := C3) (l := l) j ↔
      Nonempty (PaperGlobalIQUnitRegionTransport (C3 := C3) (l := l) j) :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.PaperMonoAnalyticUnitRegionSourceActual

end
