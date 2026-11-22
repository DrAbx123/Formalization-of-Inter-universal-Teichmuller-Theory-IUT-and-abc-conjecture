import tmp.sheaf.xif.paper.S2723GlobalIQHullActual
import tmp.sheaf.xif.paper.S3129IQHullLogVolumeSourceActual

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1LiteralIQHullFinitenessActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.XiFPaper.S2718LiteralDDataActual
open LeanFormal.IUT.XiFPaper.S2723GlobalIQHullActual
open LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual
open MeasureTheory

/-! Literal IQ hull log-volume finiteness (A482 third triangle: hull + det).

New conclusions on the literal global IQ carrier and the source-faithful local
carrier, using the existing assets (no value-realized ThetaPilotPoint hull):

* literalGlobalIQHull_measure_lt_top: Haar measure of the literal global hull
  is finite (compactness of the global unit region);
* literalGlobalIQHull_logVolume_lt_top: its Haar log-volume is finite
  (composition with the literal IQHullLogVolumeInterface);
* literalGlobalIQHull_package: compactness, Haar finiteness, log-volume
  finiteness and the unit-region point membership jointly;
* sourceIQHull_finiteness_package: local source hull finiteness together with
  the unit-region compactness and the Haar normalization
  (mass of the actual integral log-shell = 1) - the det-volume normalization
  side of the third triangle.

No sorry/axioms; no closure claim. -/

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [forall i, Fintype (C3.tensorPlaceIndex i)]

/-- Haar finiteness of the literal global hull (hull = unit region). -/
theorem literalGlobalIQHull_measure_lt_top (j : Nat) :
    globalIQHaar (C3 := C3) j (globalIQHull (C3 := C3) j) < ⊤ := by
  letI : MeasurableSpace (GlobalIQAmbient (C3 := C3) j) := borel _
  letI : BorelSpace (GlobalIQAmbient (C3 := C3) j) := ⟨rfl⟩
  haveI hAdd : Measure.IsAddHaarMeasure (globalIQHaar (C3 := C3) j) :=
    inferInstance
  haveI hFin : IsFiniteMeasureOnCompacts (globalIQHaar (C3 := C3) j) :=
    hAdd.toIsFiniteMeasureOnCompacts
  have hc : IsCompact (globalIQHull (C3 := C3) j) :=
    globalIQUnitRegion_compact (C3 := C3) j
  exact hc.measure_lt_top

/-- Haar log-volume finiteness of the literal global hull. -/
theorem literalGlobalIQHull_logVolume_lt_top (j : Nat) :
    globalIQLogVolume (C3 := C3) j (globalIQHull (C3 := C3) j) < ⊤ := by
  have h := IQHullLogVolumeInterface.hull_logVolume_lt_top
    (globalIQHullInterface (C3 := C3) j)
  simpa [globalIQHullInterface_logVolume, globalIQHullInterface_hull] using h

/-- Joint literal global hull package. -/
theorem literalGlobalIQHull_package (j : Nat) :
    IsCompact (globalIQUnitRegion (C3 := C3) j) ∧
      globalIQHaar (C3 := C3) j (globalIQHull (C3 := C3) j) < ⊤ ∧
      globalIQLogVolume (C3 := C3) j (globalIQHull (C3 := C3) j) < ⊤ ∧
      globalIQLogShellPoint (C3 := C3) j ∈ globalIQUnitRegion (C3 := C3) j :=
  ⟨globalIQUnitRegion_compact (C3 := C3) j,
   literalGlobalIQHull_measure_lt_top (C3 := C3) j,
   literalGlobalIQHull_logVolume_lt_top (C3 := C3) j,
   globalIQLogShellPoint_mem_unitRegion (C3 := C3) j⟩

/-- Local source hull finiteness + det-volume normalization package. -/
theorem sourceIQHull_finiteness_package :
    IsCompact sourceHullUnitRegion ∧
      sourceHullHaar sourceHullUnitRegion < ⊤ ∧
      sourceHullHaar (sourceIQHullLogVolume).hull < ⊤ ∧
      sourceHullHaar
        (integralLogShell (K := concreteLogShellField)
          (p := concreteRationalPrime) : Set concreteLogShellField) = 1 :=
  ⟨sourceHullUnitRegion_compact,
   sourceHullUnitRegion_logVolume_lt_top,
   sourceIQHull_hull_logVolume_lt_top,
   sourceHullHaar_integralLogShell_eq_one⟩

#check literalGlobalIQHull_measure_lt_top
#check literalGlobalIQHull_logVolume_lt_top
#check sourceIQHull_finiteness_package

end LeanFormal.IUT.XiFPaper.Mzk1LiteralIQHullFinitenessActual
end