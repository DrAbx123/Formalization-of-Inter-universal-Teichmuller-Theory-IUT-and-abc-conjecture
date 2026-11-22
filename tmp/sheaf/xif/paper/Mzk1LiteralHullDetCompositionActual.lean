import tmp.sheaf.xif.paper.S2723GlobalIQHullActual
import tmp.sheaf.xif.paper.S3129IQHullLogVolumeSourceActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1LiteralHullDetCompositionActual

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

/-! Literal hull + determinant composition (A482 third triangle: hull + det).

New conclusions composing the literal IQ hull finiteness with the existing
determinant/log-volume laws (no value-realized hull):

* literalHull_det_packet_package: literal global hull log-volume finiteness +
  positive packet determinant + packet log-volume/determinant identification;
* literalHull_det_laws_package: the same hull finiteness together with the
  determinant product and inverse laws on positive-definite factors;
* sourceHull_det_normalization_package: local source hull finiteness together
  with unit-region compactness and the Haar determinant-line normalization
  (mass of the actual integral log-shell = 1).

No sorry/axioms; no closure claim. -/

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [forall i, Fintype (C3.tensorPlaceIndex i)]

/-- Literal hull finiteness + packet determinant package. -/
theorem literalHull_det_packet_package (j : Nat) {label : Type*} [Fintype label]
    [DecidableEq label] (packet : PositivePacket label) :
    globalIQLogVolume (C3 := C3) j (globalIQHull (C3 := C3) j) < ⊤ ∧
      0 < packetDet packet ∧
      packetLogVolume packet = matrixLogDet (packetDiagonalMatrix packet) :=
  ⟨by
    have h := IQHullLogVolumeInterface.hull_logVolume_lt_top
      (globalIQHullInterface (C3 := C3) j)
    simpa [globalIQHullInterface_logVolume, globalIQHullInterface_hull] using h,
   packetDet_pos packet,
   packetLogVolume_eq_matrixLogDet packet⟩

/-- Literal hull finiteness + determinant product/packet laws package. -/
theorem literalHull_det_laws_package (j : Nat) {label : Type*} [Fintype label]
    [DecidableEq label] (packet : PositivePacket label)
    {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n Real}
    (hA : A.PosDef) (hB : B.PosDef) :
    globalIQLogVolume (C3 := C3) j (globalIQHull (C3 := C3) j) < ⊤ ∧
      matrixLogDet (A * B) = matrixLogDet A + matrixLogDet B ∧
      packetLogVolume packet = matrixLogDet (packetDiagonalMatrix packet) :=
  ⟨by
    have h := IQHullLogVolumeInterface.hull_logVolume_lt_top
      (globalIQHullInterface (C3 := C3) j)
    simpa [globalIQHullInterface_logVolume, globalIQHullInterface_hull] using h,
   matrixLogDet_mul_posDef hA hB,
   packetLogVolume_eq_matrixLogDet packet⟩

/-- Local source hull finiteness + det-line normalization package. -/
theorem sourceHull_det_normalization_package :
    sourceHullHaar (sourceIQHullLogVolume).hull < ⊤ ∧
      IsCompact sourceHullUnitRegion ∧
      sourceHullHaar
        (integralLogShell (K := concreteLogShellField)
          (p := concreteRationalPrime) : Set concreteLogShellField) = 1 :=
  ⟨sourceIQHull_hull_logVolume_lt_top,
   sourceHullUnitRegion_compact,
   sourceHullHaar_integralLogShell_eq_one⟩

#check literalHull_det_packet_package
#check literalHull_det_laws_package
#check sourceHull_det_normalization_package

end LeanFormal.IUT.XiFPaper.Mzk1LiteralHullDetCompositionActual
end