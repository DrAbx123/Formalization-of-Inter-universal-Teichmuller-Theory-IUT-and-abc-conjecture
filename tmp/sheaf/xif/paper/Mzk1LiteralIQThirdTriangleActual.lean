import tmp.sheaf.xif.paper.S2723GlobalIQHullActual
import tmp.sheaf.xif.paper.S3129IQHullLogVolumeSourceActual

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1LiteralIQThirdTriangleActual

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

/-! Literal IQ third triangle: lower-bound transfer + finiteness (hull side),

and its composition with the det-volume normalization.  New conclusions using
existing assets (S2723 literal global IQ carrier, S3129 source-faithful local
carrier); no value-realized ThetaPilotPoint hull is used.

* literalHull_lowerBound_transfer: any ENNReal lower bound on the literal
  unit-region log-volume transfers to the literal hull and the hull
  log-volume is finite (the two conclusions of the paper s Cor 3.12 argument);
* literalHull_det_normalization: the local source hull log-volume is finite
  together with the actual Haar normalization of the integral log-shell
  (det-line volume one) - the hull+det reading.

No sorry/axioms; no closure claim. -/

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [forall i, Fintype (C3.tensorPlaceIndex i)]

/-- Lower-bound transfer to the literal hull + hull log-volume finiteness. -/
theorem literalHull_lowerBound_transfer (j : Nat) {lowerBound : ENNReal}
    (h : lowerBound ≤ globalIQLogVolume (C3 := C3) j
      (globalIQUnitRegion (C3 := C3) j)) :
    lowerBound ≤ globalIQLogVolume (C3 := C3) j (globalIQHull (C3 := C3) j) ∧
      globalIQLogVolume (C3 := C3) j (globalIQHull (C3 := C3) j) < ⊤ := by
  have hmain := IQHullLogVolumeInterface.lower_bound_and_finiteness
    (globalIQHullInterface (C3 := C3) j) h
  simpa [globalIQHullInterface_logVolume, globalIQHullInterface_hull] using hmain

/-- Local source hull finiteness + det-line Haar normalization (hull + det). -/
theorem literalHull_det_normalization :
    sourceHullHaar (sourceIQHullLogVolume).hull < ⊤ ∧
      sourceHullHaar
        (integralLogShell (K := concreteLogShellField)
          (p := concreteRationalPrime) : Set concreteLogShellField) = 1 :=
  ⟨sourceIQHull_hull_logVolume_lt_top,
   sourceHullHaar_integralLogShell_eq_one⟩

/-- Joint third-triangle package: literal hull finiteness on both carriers plus
the det-line normalization. -/
theorem literalIQ_thirdTriangle_package (j : Nat) :
    globalIQLogVolume (C3 := C3) j (globalIQHull (C3 := C3) j) < ⊤ ∧
      sourceHullHaar (sourceIQHullLogVolume).hull < ⊤ ∧
      sourceHullHaar
        (integralLogShell (K := concreteLogShellField)
          (p := concreteRationalPrime) : Set concreteLogShellField) = 1 :=
  ⟨by
    have h := IQHullLogVolumeInterface.hull_logVolume_lt_top
      (globalIQHullInterface (C3 := C3) j)
    simpa [globalIQHullInterface_logVolume, globalIQHullInterface_hull] using h,
   sourceIQHull_hull_logVolume_lt_top,
   sourceHullHaar_integralLogShell_eq_one⟩

#check literalHull_lowerBound_transfer
#check literalHull_det_normalization
#check literalIQ_thirdTriangle_package

end LeanFormal.IUT.XiFPaper.Mzk1LiteralIQThirdTriangleActual
end