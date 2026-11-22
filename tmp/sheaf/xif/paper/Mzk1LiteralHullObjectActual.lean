import tmp.sheaf.xif.paper.Mzk1LiteralIQHullFinitenessActual

/-!
# O7/O8 literal hull + det object reference

Reuses the green `Mzk1LiteralIQHullFinitenessActual`: literal global IQ hull
Haar/log-volume finiteness (O7 hull) and the source hull finiteness + det-volume
normalization (O8 det side).  This file exposes the proved statements under a
stable namespace for the 3.12 object layer.

No sorry, axiom, True or placeholder.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1LiteralHullObjectActual

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
open LeanFormal.IUT.XiFPaper.Mzk1LiteralIQHullFinitenessActual
open MeasureTheory

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [forall i, Fintype (C3.tensorPlaceIndex i)]

/-- O7: Haar measure of the literal global hull is finite. -/
theorem literalHull_haar_finite (j : Nat) :
    globalIQHaar (C3 := C3) j (globalIQHull (C3 := C3) j) < ⊤ :=
  literalGlobalIQHull_measure_lt_top (C3 := C3) j

/-- O7: Haar log-volume of the literal global hull is finite. -/
theorem literalHull_logVolume_finite (j : Nat) :
    globalIQLogVolume (C3 := C3) j (globalIQHull (C3 := C3) j) < ⊤ :=
  literalGlobalIQHull_logVolume_lt_top (C3 := C3) j

/-- O7: compactness + Haar finiteness + log-volume finiteness of the literal hull. -/
theorem literalHull_package (j : Nat) :
    IsCompact (globalIQUnitRegion (C3 := C3) j) ∧
      globalIQHaar (C3 := C3) j (globalIQHull (C3 := C3) j) < ⊤ ∧
      globalIQLogVolume (C3 := C3) j (globalIQHull (C3 := C3) j) < ⊤ ∧
      globalIQLogShellPoint (C3 := C3) j ∈ globalIQUnitRegion (C3 := C3) j :=
  literalGlobalIQHull_package (C3 := C3) j

/-- O8: local source hull finiteness + det-volume normalization package. -/
theorem sourceHull_detVolume_package :
    IsCompact sourceHullUnitRegion ∧
      sourceHullHaar sourceHullUnitRegion < ⊤ ∧
      sourceHullHaar (sourceIQHullLogVolume).hull < ⊤ ∧
      sourceHullHaar
        (integralLogShell (K := concreteLogShellField)
          (p := concreteRationalPrime) : Set concreteLogShellField) = 1 :=
  sourceIQHull_finiteness_package

end LeanFormal.IUT.XiFPaper.Mzk1LiteralHullObjectActual
